"""Fixture authority, public replay, and deterministic-report tests."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

PACKAGE = Path(__file__).resolve().parents[1]
ROOT = PACKAGE.parents[1]
sys.path.insert(0, str(PACKAGE))

PUBLIC_MODEL_MODULES = (
    "__init__.py",
    "analysis.py",
    "commitment.py",
    "committed.py",
    "classical.py",
    "classical_fixtures.py",
    "field.py",
    "fixtures.py",
    "native.py",
    "profile.py",
    "proof.py",
    "provenance.py",
    "report.py",
    "subjects.py",
    "terms.py",
    "transcript.py",
)

import friiormodel.fixtures as fixtures  # noqa: E402
import friiormodel.report as report_module  # noqa: E402
from friiormodel.committed import verify_committed_fri  # noqa: E402
from friiormodel.fixtures import (  # noqa: E402
    load_fixture,
    parse_expected_projection,
    parse_negative_proofs,
    parse_private_generation,
    parse_public_inputs,
    parse_public_native_vector,
    parse_public_proof,
    parse_relation_initial_oracle,
    parse_replay_policy,
)
from friiormodel.report import (  # noqa: E402
    SOURCE_BASES,
    _source_closure,
    build_public_report,
    canonical_pretty_json,
    expected_projection,
    verify_public_report,
)
from friiormodel.provenance import (  # noqa: E402
    MAX_JSON_DEPTH,
    MAX_JSON_NODES,
    MAX_STRING_BYTES,
)
from friiormodel.terms import ModelFailure, ResourceCounter  # noqa: E402


def _loaded(name: str):
    return load_fixture(ROOT, f"evaluation/native-fri-ior/cases/{name}", name)


class FrozenFixtureTest(unittest.TestCase):
    def test_all_public_parsers_round_trip_exact_terms(self) -> None:
        inputs = parse_public_inputs(_loaded("public-inputs.json").value)
        proof = parse_public_proof(_loaded("public-proof.json").value)
        trace = parse_public_native_vector(_loaded("public-native-vector.json").value)
        limits = parse_replay_policy(_loaded("replay-policy.json").value)
        self.assertEqual(inputs.to_term(), _loaded("public-inputs.json").value)
        self.assertEqual(proof.to_term(), _loaded("public-proof.json").value)
        self.assertEqual(
            trace.identity.to_term(),
            _loaded("public-native-vector.json").value["native_trace_id"],
        )
        self.assertGreater(limits.proof_bytes, proof.canonical_byte_length)

        classical_limits = report_module.parse_classical_replay_policy(
            _loaded("exact-classical-replay-policy.json").value
        )
        self.assertEqual(classical_limits.logical_query_occurrences, 12)

    def test_parsers_reject_extra_keys_bad_enums_and_duplicate_json_keys(self) -> None:
        inputs = deepcopy(_loaded("public-inputs.json").value)
        inputs["extra"] = False
        with self.assertRaises(ModelFailure):
            parse_public_inputs(inputs)
        vector = deepcopy(_loaded("public-native-vector.json").value)
        vector["events"][0]["kind"] = "Unknown"
        with self.assertRaises(ModelFailure):
            parse_public_native_vector(vector)
        with self.assertRaises(ModelFailure):
            fixtures.load_bounded_json_bytes(b'{"schema":"a","schema":"b"}')

    def test_expected_projection_has_a_checked_schema_and_exact_shape(self) -> None:
        value = deepcopy(_loaded("expected-results.json").value)
        parsed = parse_expected_projection(value)
        self.assertEqual(parsed, value)
        self.assertEqual(
            parsed["authority"],
            "regression-golden-not-semantic-or-provenance-authority",
        )
        value["schema"] = "unknown"
        with self.assertRaises(ModelFailure):
            parse_expected_projection(value)

    def test_private_generation_parser_requires_explicit_owner_local_authority(
        self,
    ) -> None:
        value = deepcopy(_loaded("owner-generation-input.json").value)
        parsed = parse_private_generation(value)
        self.assertEqual(len(parsed.coefficients), 8)
        self.assertEqual(len(parsed.initial_layer_salts), 8)
        self.assertEqual(len(parsed.first_fold_layer_salts), 4)
        value["authority"] = "public-report-input"
        with self.assertRaises(ModelFailure) as caught:
            parse_private_generation(value)
        self.assertEqual(caught.exception.code, "FRI-IOR-FIXTURE-030")

        value = deepcopy(_loaded("owner-generation-input.json").value)
        value["disclosure"]["contains_real_secret"] = True
        with self.assertRaises(ModelFailure) as caught:
            parse_private_generation(value)
        self.assertEqual(caught.exception.code, "FRI-IOR-FIXTURE-030")

    def test_relation_oracle_parser_requires_its_independent_owner_lane(self) -> None:
        value = deepcopy(_loaded("owner-relation-input.json").value)
        oracle = parse_relation_initial_oracle(value)
        self.assertEqual(oracle.name, "O0")
        value["authority"] = "construction-receipt-derived"
        with self.assertRaises(ModelFailure) as caught:
            parse_relation_initial_oracle(value)
        self.assertEqual(caught.exception.code, "FRI-IOR-FIXTURE-034")

        value = deepcopy(_loaded("owner-relation-input.json").value)
        value["nonclaims"].pop()
        with self.assertRaises(ModelFailure) as caught:
            parse_relation_initial_oracle(value)
        self.assertEqual(caught.exception.code, "FRI-IOR-FIXTURE-034")

    def test_mixed_root_is_refused_before_file_loading(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ModelFailure) as caught:
                build_public_report(Path(directory))
        self.assertEqual(caught.exception.code, "FRI-IOR-FIXTURE-003")

    def test_two_late_negative_proofs_reach_distinct_refusal_boundaries(self) -> None:
        inputs = parse_public_inputs(_loaded("public-inputs.json").value)
        limits = parse_replay_policy(_loaded("replay-policy.json").value)
        negatives = parse_negative_proofs(_loaded("public-negative-proofs.json").value)
        codes = {
            name: verify_committed_fri(inputs, proof, ResourceCounter(limits)).code
            for name, proof in negatives.items()
        }
        self.assertEqual(
            codes,
            {
                "authenticated-fold-inconsistency": "FRI-IOR-COMMITTED-020",
                "fold-consistent-terminal-degree-excess": "FRI-IOR-COMMITTED-022",
            },
        )


class PublicReportTest(unittest.TestCase):
    def test_report_is_verified_byte_stable_and_matches_frozen_projection(self) -> None:
        first = build_public_report(ROOT)
        second = build_public_report(ROOT)
        self.assertTrue(verify_public_report(ROOT, first))
        self.assertEqual(canonical_pretty_json(first), canonical_pretty_json(second))
        frozen = parse_expected_projection(_loaded("expected-results.json").value)
        self.assertEqual(expected_projection(first), frozen["projection"])

    def test_report_loader_never_opens_private_or_expected_lanes(self) -> None:
        opened: list[str] = []
        original = fixtures._read_regular_file

        def traced(root: Path, relative: str, maximum: int):
            opened.append(relative)
            return original(root, relative, maximum)

        with (
            patch("friiormodel.fixtures._read_regular_file", side_effect=traced),
            patch("friiormodel.report._read_regular_file", side_effect=traced),
        ):
            self.assertTrue(verify_public_report(ROOT, build_public_report(ROOT)))
        joined = "\n".join(opened)
        self.assertNotIn("owner-generation-input", joined)
        self.assertNotIn("expected-results", joined)
        self.assertNotIn("owner-relation-input", joined)
        self.assertNotIn("exact-classical-owner-generation-input", joined)

    def test_public_report_never_imports_generation_or_names_private_expected_paths(
        self,
    ) -> None:
        source = (PACKAGE / "friiormodel/report.py").read_text(encoding="utf-8")
        self.assertNotIn("friiormodel.generation", source)
        self.assertNotIn("friiormodel.constructions", source)
        self.assertNotIn("friiormodel.relations", source)
        self.assertNotIn("owner-generation-input.json", source)
        self.assertNotIn("expected-results.json", source)
        self.assertNotIn("owner-relation-input.json", source)
        self.assertNotIn("exact-classical-owner-generation-input.json", source)

    def test_report_source_basis_is_the_complete_public_local_import_closure(
        self,
    ) -> None:
        closure = set(_source_closure(ROOT, SOURCE_BASES["report"]))
        self.assertEqual(
            closure,
            {
                *PUBLIC_MODEL_MODULES,
                "../independent.py",
                "../classical_independent.py",
                "../run.py",
            },
        )
        self.assertTrue(
            {
                "generation.py",
                "constructions.py",
                "relations.py",
                "diagnostics.py",
            }.isdisjoint(closure)
        )

    def test_independent_replay_uses_only_frozen_public_terms(self) -> None:
        import independent

        inputs = _loaded("public-inputs.json").value
        proof = _loaded("public-proof.json").value
        limits = _loaded("replay-policy.json").value["limits"]
        result = independent.verify_public_fri(inputs, proof, limits=limits)
        self.assertEqual(
            (result["outcome"], result["code"]),
            ("Affirmative", "FRI-IOR-INDEPENDENT-100"),
        )

    def test_report_passes_raw_frozen_terms_to_independent_replay(self) -> None:
        actual = report_module._load_independent()
        calls: list[tuple[object, object, object]] = []

        class RecordingIndependent:
            @staticmethod
            def verify_public_fri(inputs, proof, *, limits):
                calls.append((inputs, proof, limits))
                return actual.verify_public_fri(inputs, proof, limits=limits)

        with patch(
            "friiormodel.report._load_independent",
            return_value=RecordingIndependent(),
        ):
            build_public_report(ROOT)
        self.assertEqual(
            calls,
            [
                (
                    _loaded("public-inputs.json").value,
                    _loaded("public-proof.json").value,
                    _loaded("replay-policy.json").value["limits"],
                )
            ],
        )

    def test_exact_classical_public_path_uses_only_raw_frozen_terms(self) -> None:
        actual = report_module._load_classical_independent()
        calls: list[tuple[object, object, object]] = []

        class RecordingIndependent:
            @staticmethod
            def verify_public_classical_fri(inputs, proof, *, limits):
                calls.append((inputs, proof, limits))
                return actual.verify_public_classical_fri(
                    inputs,
                    proof,
                    limits=limits,
                )

        with (
            patch(
                "friiormodel.report._load_classical_independent",
                return_value=RecordingIndependent(),
            ),
            patch(
                "friiormodel.classical.verify_committed_fiat_shamir",
                side_effect=AssertionError("producer verifier is not public authority"),
            ),
        ):
            built = build_public_report(ROOT)
        self.assertEqual(
            calls,
            [
                (
                    _loaded("exact-classical-public-inputs.json").value,
                    _loaded("exact-classical-public-proof.json").value,
                    _loaded("exact-classical-replay-policy.json").value["limits"],
                )
            ],
        )
        exact = built["report"]["exact_classical_execution"]
        self.assertEqual(
            (exact["independent_replay"]["outcome"], exact["independent_replay"]["code"]),
            ("Affirmative", "FRI-IOR-CLASSICAL-INDEPENDENT-100"),
        )
        self.assertFalse(exact["uses_owner_generation_input"])

    def test_report_policy_rejects_self_authored_negative_success(self) -> None:
        positive = parse_public_proof(_loaded("public-proof.json").value)
        with patch(
            "friiormodel.report.parse_negative_proofs",
            return_value={
                "authenticated-fold-inconsistency": positive,
                "fold-consistent-terminal-degree-excess": positive,
            },
        ):
            report = build_public_report(ROOT)
            self.assertFalse(verify_public_report(ROOT, report))

    def test_report_verifier_is_total_on_malformed_nested_shapes(self) -> None:
        paths = (
            ("positive_execution",),
            ("positive_execution", "native", "result"),
            ("positive_execution", "independent_replay"),
            ("positive_execution", "reconciliation"),
            ("negative_executions", 0, "result"),
            ("analysis_question_formation", 0, "result"),
        )
        for path in paths:
            with self.subTest(path=path):
                report = deepcopy(build_public_report(ROOT))
                cursor = report["report"]
                for component in path[:-1]:
                    cursor = cursor[component]
                cursor[path[-1]] = []
                report["report_content_id"] = str(
                    report_module.canonical_json_content_id(report["report"])
                )
                self.assertFalse(verify_public_report(ROOT, report))

    def test_report_verifier_is_total_on_non_json_and_boundedness_failures(
        self,
    ) -> None:
        nested: object = None
        for _ in range(MAX_JSON_DEPTH + 1):
            nested = [nested]
        cases = (
            b"not-json",
            0.5,
            object(),
            "\ud800",
            10**5000,
            nested,
            "x" * (MAX_STRING_BYTES + 1),
            [None] * (MAX_JSON_NODES + 1),
        )
        for malformed_value in cases:
            with self.subTest(value_type=type(malformed_value).__name__):
                candidate = deepcopy(build_public_report(ROOT))
                candidate["report"]["malformed"] = malformed_value
                self.assertFalse(verify_public_report(ROOT, candidate))

    def test_report_verifier_is_total_on_unhashable_negative_names(self) -> None:
        for malformed_name in ([], {}):
            with self.subTest(value_type=type(malformed_name).__name__):
                candidate = deepcopy(build_public_report(ROOT))
                candidate["report"]["negative_executions"][0]["name"] = (
                    malformed_name
                )
                candidate["report_content_id"] = str(
                    report_module.canonical_json_content_id(candidate["report"])
                )
                self.assertFalse(verify_public_report(ROOT, candidate))

    def test_minimal_copied_checkout_replays_without_private_expected_or_git(
        self,
    ) -> None:
        self.assertTrue(
            {
                "generation.py",
                "constructions.py",
                "diagnostics.py",
                "relations.py",
            }.isdisjoint(PUBLIC_MODEL_MODULES)
        )
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "checkout"
            package = copied / "evaluation/native-fri-ior"
            (package / "friiormodel").mkdir(parents=True)
            for name in PUBLIC_MODEL_MODULES:
                shutil.copy2(
                    PACKAGE / "friiormodel" / name,
                    package / "friiormodel" / name,
                )
            shutil.copy2(PACKAGE / "independent.py", package / "independent.py")
            shutil.copy2(
                PACKAGE / "classical_independent.py",
                package / "classical_independent.py",
            )
            shutil.copy2(PACKAGE / "run.py", package / "run.py")
            (package / "cases").mkdir()
            for name in (
                "public-inputs.json",
                "public-proof.json",
                "public-native-vector.json",
                "public-negative-proofs.json",
                "replay-policy.json",
                "exact-classical-public-inputs.json",
                "exact-classical-public-proof.json",
                "exact-classical-replay-policy.json",
                "source-ledger.json",
            ):
                shutil.copy2(PACKAGE / "cases" / name, package / "cases" / name)
            self.assertFalse((copied / ".git").exists())
            self.assertFalse(
                (package / "cases/owner-generation-input.json").exists()
            )
            self.assertFalse((package / "cases/expected-results.json").exists())
            self.assertFalse((package / "cases/owner-relation-input.json").exists())
            self.assertFalse(
                (package / "cases/exact-classical-owner-generation-input.json").exists()
            )
            self.assertFalse((package / "friiormodel/generation.py").exists())
            self.assertFalse((package / "friiormodel/constructions.py").exists())
            self.assertFalse((package / "friiormodel/diagnostics.py").exists())
            self.assertFalse((package / "friiormodel/relations.py").exists())
            result = subprocess.run(
                [sys.executable, str(package / "run.py"), "--root", str(copied)],
                cwd=copied,
                capture_output=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr.decode())
            self.assertEqual(
                result.stdout,
                canonical_pretty_json(build_public_report(ROOT)),
            )

    def test_private_and_expected_file_mutations_do_not_change_public_report(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "checkout"
            package = copied / "evaluation/native-fri-ior"
            shutil.copytree(
                PACKAGE,
                package,
                ignore=shutil.ignore_patterns("__pycache__", ".pytest_cache"),
            )
            command = [sys.executable, str(package / "run.py"), "--root", str(copied)]
            baseline = subprocess.run(
                command, cwd=copied, capture_output=True, check=True
            ).stdout
            (package / "cases/owner-generation-input.json").write_text(
                '{"ignored":"private mutation"}\n', encoding="utf-8"
            )
            (package / "cases/expected-results.json").write_text(
                '{"ignored":"expected mutation"}\n', encoding="utf-8"
            )
            (package / "cases/owner-relation-input.json").write_text(
                '{"ignored":"relation mutation"}\n', encoding="utf-8"
            )
            (package / "cases/exact-classical-owner-generation-input.json").write_text(
                '{"ignored":"exact owner mutation"}\n', encoding="utf-8"
            )
            changed = subprocess.run(
                command, cwd=copied, capture_output=True, check=True
            ).stdout
            self.assertEqual(changed, baseline)


if __name__ == "__main__":
    unittest.main()
