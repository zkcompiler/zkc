"""Closed diagnostic inventory and evidence-classification tests."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import textwrap
import unittest


PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE))

from friiormodel.diagnostics import (  # noqa: E402
    DiagnosticClassification,
    EvidenceClass,
    check_diagnostic_contract,
)
from friiormodel.profile import admit_exact_profile  # noqa: E402
from friiormodel.terms import ModelFailure, OutcomeClass, semantic_id  # noqa: E402


def _code(suffix: str) -> str:
    """Build synthetic identifiers without adding literal test mentions."""

    return "FRI-IOR-" + suffix


def _direct(code: str) -> dict[str, DiagnosticClassification]:
    return {
        code: DiagnosticClassification(
            EvidenceClass.DIRECT_PUBLIC_SURFACE,
            "synthetic ordinary public result boundary",
        )
    }


def _write_tree(
    root: Path,
    production: dict[str, str],
    tests: dict[str, str] | None = None,
) -> None:
    for relative, source in production.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(source), encoding="utf-8")
    for relative, source in (tests or {}).items():
        path = root / "tests" / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(source), encoding="utf-8")


def _emission_source(
    code: str,
    *,
    boundary: str = "synthetic:surface",
    outcome: str = "MALFORMED",
) -> str:
    return f"""\
        from friiormodel.terms import CheckResult, OutcomeClass

        def run():
            return CheckResult(
                OutcomeClass.{outcome},
                {boundary!r},
                {code!r},
                "synthetic result",
            )
    """


class CurrentDiagnosticContractTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.admission = check_diagnostic_contract()
        if cls.admission.result.outcome is not OutcomeClass.AFFIRMATIVE:
            raise AssertionError(cls.admission.result.to_term())
        assert cls.admission.report is not None
        cls.report = cls.admission.report

    def test_inventory_is_closed_dynamic_and_machine_readable(self) -> None:
        paths = {path for path, _ in self.report.production_sources}
        self.assertIn("independent.py", paths)
        self.assertIn("friiormodel/diagnostics.py", paths)
        self.assertIn("friiormodel/fixtures.py", paths)
        self.assertEqual(
            set(self.report.by_code), {entry.code for entry in self.report.entries}
        )
        encoded = json.dumps(
            self.report.to_term(),
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        self.assertGreater(len(encoded), 1000)
        self.assertEqual(len(self.report.validation_basis_id.digest), 64)
        self.assertIsNone(self.admission.result.subject)
        self.assertEqual(
            self.admission.result.evidence["validation_basis_id"],
            str(self.report.validation_basis_id),
        )
        self.assertTrue(
            all(len(digest) == 64 for _, digest in self.report.production_sources)
        )

    def test_all_five_evidence_classes_are_explicit(self) -> None:
        classes = {entry.classification.evidence_class for entry in self.report.entries}
        self.assertEqual(classes, set(EvidenceClass))
        for entry in self.report.entries:
            if (
                entry.classification.evidence_class
                is not EvidenceClass.DIRECT_PUBLIC_SURFACE
            ):
                self.assertTrue(entry.classification.reason.strip())

    def test_static_test_mentions_are_not_reported_as_reachability(self) -> None:
        entry = self.report.by_code["FRI-IOR-PROFILE-017"]
        self.assertGreater(len(entry.test_mentions), 0)
        self.assertTrue(
            any(mention.assertion_context for mention in entry.test_mentions)
        )
        term = entry.to_term()
        self.assertEqual(
            term["reachability_status"],
            "not-established-by-static-inventory",
        )
        self.assertTrue(
            all(
                mention["establishes_reachability"] is False
                for mention in term["static_test_mentions"]
            )
        )

    def test_runtime_supplied_boundary_is_not_invented(self) -> None:
        entry = self.report.by_code["FRI-IOR-CHECKER-001"]
        self.assertEqual(entry.boundaries, ())
        self.assertEqual(entry.to_term()["boundary_recovery"], "runtime-supplied")
        self.assertEqual(entry.outcomes, (OutcomeClass.CHECKER_FAILURE.value,))

    def test_representative_public_first_boundary_matches_inventory(self) -> None:
        result = admit_exact_profile({"name": "not-a-formed-profile"})
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-PROFILE-017")
        entry = self.report.by_code[result.code]
        self.assertEqual(entry.owner_module, "friiormodel.profile")
        self.assertEqual(entry.boundaries, (result.boundary,))
        self.assertEqual(entry.outcomes, (result.outcome.value,))
        self.assertIs(
            entry.classification.evidence_class,
            EvidenceClass.DIRECT_PUBLIC_SURFACE,
        )

    def test_representative_formation_failure_stays_separate(self) -> None:
        with self.assertRaises(ModelFailure) as caught:
            semantic_id("BadKind", "valid.domain", {})
        self.assertEqual(caught.exception.code, "FRI-IOR-IDENTITY-001")
        entry = self.report.by_code[caught.exception.code]
        self.assertEqual(entry.boundaries, (caught.exception.boundary,))
        self.assertIs(entry.classification.evidence_class, EvidenceClass.FORMATION)


class SyntheticDiagnosticContractTest(unittest.TestCase):
    def test_later_module_and_assertion_mention_are_discovered(self) -> None:
        code = _code("SYNTH-001")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(
                root,
                {"future/module.py": _emission_source(code)},
                {
                    "test_future.py": f"""\
                        def test_surface():
                            assert {code!r}
                    """,
                },
            )
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        assert admission.report is not None
        entry = admission.report.by_code[code]
        self.assertEqual(entry.owner_module, "future.module")
        self.assertEqual(entry.boundaries, ("synthetic:surface",))
        self.assertEqual(entry.outcomes, (OutcomeClass.MALFORMED.value,))
        self.assertEqual(len(entry.test_mentions), 1)
        self.assertTrue(entry.test_mentions[0].assertion_context)
        self.assertFalse(entry.test_mentions[0].to_term()["establishes_reachability"])

    def test_new_identifier_fails_until_classified(self) -> None:
        code = _code("SYNTH-002")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"later.py": _emission_source(code)})
            admission = check_diagnostic_contract(root, classifications={})
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-015")
        self.assertEqual(admission.result.evidence["missing"], [code])

    def test_stale_classification_is_rejected(self) -> None:
        code = _code("SYNTH-003")
        stale = _code("SYNTH-004")
        classifications = {
            **_direct(code),
            **_direct(stale),
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": _emission_source(code)})
            admission = check_diagnostic_contract(
                root,
                classifications=classifications,
            )
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-016")
        self.assertEqual(admission.result.evidence["stale"], [stale])

    def test_unknown_literal_test_identifier_is_rejected(self) -> None:
        code = _code("SYNTH-005")
        unknown = _code("UNKNOWN-001")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(
                root,
                {"one.py": _emission_source(code)},
                {"test_unknown.py": f"assert {unknown!r}\n"},
            )
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-018")
        self.assertEqual(admission.result.evidence["unknown_test_ids"], [unknown])

    def test_inconsistent_duplicate_owner_is_rejected(self) -> None:
        code = _code("SYNTH-006")
        source = _emission_source(code)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source, "two.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-010")
        self.assertEqual(admission.result.evidence["owners"], ["one", "two"])

    def test_inconsistent_duplicate_boundary_is_rejected(self) -> None:
        code = _code("SYNTH-007")
        source = _emission_source(code, boundary="synthetic:one") + _emission_source(
            code,
            boundary="synthetic:two",
        ).replace("def run():", "def run_again():")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-012")
        self.assertEqual(
            admission.result.evidence["boundaries"],
            ["synthetic:one", "synthetic:two"],
        )

    def test_inconsistent_duplicate_outcome_is_rejected(self) -> None:
        code = _code("SYNTH-008")
        source = _emission_source(code) + _emission_source(
            code,
            outcome="REFUSED",
        ).replace("def run():", "def run_again():")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-013")
        self.assertEqual(
            admission.result.evidence["outcomes"],
            [OutcomeClass.MALFORMED.value, OutcomeClass.REFUSED.value],
        )

    def test_unmapped_forwarding_helper_has_no_silent_outcome(self) -> None:
        code = _code("SYNTH-009")
        source = f"""\
            from friiormodel.terms import CheckResult, OutcomeClass

            def custom_failure(code):
                return CheckResult(
                    OutcomeClass.MALFORMED,
                    "synthetic:helper",
                    code,
                    "synthetic result",
                )

            def run():
                return custom_failure({code!r})
        """
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-013")
        self.assertEqual(admission.result.evidence["outcomes"], [])

    def test_unrecognized_diagnostic_id_wrapper_fails_closed(self) -> None:
        code = _code("SYNTH-011")
        source = f"""\
            from friiormodel.terms import CheckResult, OutcomeClass

            def custom_failure(diagnostic_id):
                return CheckResult(
                    OutcomeClass.MALFORMED,
                    "synthetic:helper",
                    diagnostic_id,
                    "synthetic result",
                )

            def run():
                return custom_failure({code!r})
        """
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-007")
        self.assertEqual(admission.result.evidence["module"], "one")
        self.assertEqual(admission.result.evidence["literals"][0]["code"], code)

    def test_recursively_constant_code_concatenation_is_inventoried(self) -> None:
        code = _code("SYNTH-014")
        source = """\
            from friiormodel.terms import CheckResult, OutcomeClass

            PREFIX = "FRI-" + "IOR-"

            def run():
                suffix = "SYNTH-" + "014"
                return CheckResult(
                    OutcomeClass.MALFORMED,
                    "synthetic:surface",
                    PREFIX + suffix,
                    "synthetic result",
                )
        """
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        assert admission.report is not None
        self.assertEqual(set(admission.report.by_code), {code})

    def test_helper_returned_code_expression_fails_closed(self) -> None:
        code = _code("SYNTH-015")
        source = """\
            from friiormodel.terms import CheckResult, OutcomeClass

            def make_code():
                return "-".join(("FRI", "IOR", "SYNTH", "015"))

            def run():
                return CheckResult(
                    OutcomeClass.MALFORMED,
                    "synthetic:surface",
                    make_code(),
                    "synthetic result",
                )
        """
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-007")
        self.assertIsNone(admission.report)
        self.assertEqual(admission.result.evidence["literals"], [])
        self.assertEqual(
            admission.result.evidence["unresolved_emitters"],
            [
                {
                    "emitter": "CheckResult",
                    "function": "run",
                    "line": 7,
                    "reason": "code-expression-is-not-statically-closed",
                }
            ],
        )

    def test_imported_emitter_alias_with_dynamic_code_fails_closed(self) -> None:
        code = _code("SYNTH-017")
        source = f'''\
            from friiormodel.terms import CheckResult, CheckResult as CR, OutcomeClass

            def known():
                return CheckResult(
                    OutcomeClass.MALFORMED,
                    "synthetic:known",
                    {code!r},
                    "known result",
                )

            def make_new_code():
                return "-".join(("FRI", "IOR", "SYNTH", "997"))

            def escaped():
                return CR(
                    OutcomeClass.MALFORMED,
                    "synthetic:escaped",
                    make_new_code(),
                    "escaped result",
                )
        '''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-007")
        self.assertIsNone(admission.report)
        unresolved = admission.result.evidence["unresolved_emitters"]
        self.assertEqual(len(unresolved), 1)
        self.assertEqual(unresolved[0]["emitter"], "CR")
        self.assertEqual(unresolved[0]["function"], "escaped")
        self.assertEqual(
            unresolved[0]["reason"],
            "code-expression-is-not-statically-closed",
        )

    def test_transitive_assignment_emitter_alias_fails_closed(self) -> None:
        code = _code("SYNTH-019")
        source = f'''\
            from friiormodel.terms import CheckResult, OutcomeClass

            Alias = CheckResult
            CR = Alias

            def known():
                return CheckResult(
                    OutcomeClass.MALFORMED,
                    "synthetic:known",
                    {code!r},
                    "known result",
                )

            def make_new_code():
                return "-".join(("FRI", "IOR", "SYNTH", "998"))

            def escaped():
                return CR(
                    OutcomeClass.MALFORMED,
                    "synthetic:escaped",
                    make_new_code(),
                    "escaped result",
                )
        '''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-007")
        self.assertIsNone(admission.report)
        unresolved = admission.result.evidence["unresolved_emitters"]
        self.assertEqual(len(unresolved), 1)
        self.assertEqual(unresolved[0]["emitter"], "CR")
        self.assertEqual(unresolved[0]["function"], "escaped")

    def test_fixed_code_helper_does_not_require_a_code_at_its_call_site(self) -> None:
        code = _code("SYNTH-016")
        source = f"""\
            from friiormodel.terms import CheckResult, OutcomeClass

            def fixed_failure():
                return CheckResult(
                    OutcomeClass.MALFORMED,
                    "synthetic:surface",
                    {code!r},
                    "synthetic result",
                )

            def run():
                return fixed_failure()
        """
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": source})
            admission = check_diagnostic_contract(root, classifications=_direct(code))
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        assert admission.report is not None
        self.assertEqual(
            admission.report.by_code[code].sites[0].function,
            "fixed_failure",
        )

    def test_forged_non_direct_row_without_reason_is_rejected(self) -> None:
        code = _code("SYNTH-010")
        forged = object.__new__(DiagnosticClassification)
        object.__setattr__(forged, "evidence_class", EvidenceClass.FORMATION)
        object.__setattr__(forged, "reason", "")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": _emission_source(code)})
            admission = check_diagnostic_contract(
                root,
                classifications={code: forged},
            )
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-017")
        self.assertEqual(admission.result.evidence["diagnostics"], [code])

    def test_forged_row_with_untyped_evidence_class_is_malformed(self) -> None:
        code = _code("SYNTH-012")
        forged = object.__new__(DiagnosticClassification)
        object.__setattr__(forged, "evidence_class", "formation")
        object.__setattr__(forged, "reason", "not a typed evidence class")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": _emission_source(code)})
            admission = check_diagnostic_contract(
                root,
                classifications={code: forged},
            )
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-014")
        self.assertEqual(admission.result.evidence["rows"], [code])

    def test_forged_row_without_fields_is_malformed(self) -> None:
        code = _code("SYNTH-013")
        forged = object.__new__(DiagnosticClassification)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _write_tree(root, {"one.py": _emission_source(code)})
            admission = check_diagnostic_contract(
                root,
                classifications={code: forged},
            )
        self.assertEqual(admission.result.code, "FRI-IOR-DIAGNOSTIC-014")
        self.assertEqual(admission.result.evidence["rows"], [code])


if __name__ == "__main__":
    unittest.main()
