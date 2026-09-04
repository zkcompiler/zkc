from __future__ import annotations

from contextlib import contextmanager
import copy
import hashlib
import inspect
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from typing import Any, Iterator


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(MODEL_ROOT))

from p01model.provenance import (  # noqa: E402
    ArtifactContentId,
    EvidenceRecordId,
    ProvenanceError,
    RootBindingError,
    ValidationBasisId,
    artifact_content_id,
    canonical_json_bytes,
    canonical_json_content_id,
    canonical_json_text,
    load_bounded_json_bytes,
    load_public_fixture,
)
from p01model.report import (  # noqa: E402
    EXPECTED_PROJECTION_SCHEMA,
    SCHEMA,
    build_report,
    expected_projection,
    verify_report,
)


RUNNER_PATH = "evaluation/r2-p01-schnorr/run.py"
PUBLIC_INPUT_PATH = "evaluation/r2-p01-schnorr/cases/public-inputs.json"
SOURCE_LEDGER_PATH = "evaluation/r2-p01-schnorr/cases/source-ledger.json"
EXPECTED_PATH = "evaluation/r2-p01-schnorr/cases/expected-results.json"
PRIVATE_SIDECAR_PATH = "evaluation/r2-p01-schnorr/cases/private-generation.json"

# This is intentionally explicit. A copied replay succeeds from exactly the
# public fixture/oracle and the complete source closure consumed by report.py.
# In particular, neither the private generation sidecar nor the tests are part
# of the portable replay packet.
COPY_ALLOWLIST = (
    EXPECTED_PATH,
    PUBLIC_INPUT_PATH,
    SOURCE_LEDGER_PATH,
    "evaluation/r2-p01-schnorr/p01model/__init__.py",
    "evaluation/r2-p01-schnorr/p01model/analysis.py",
    "evaluation/r2-p01-schnorr/p01model/diagnostics.py",
    "evaluation/r2-p01-schnorr/p01model/execution.py",
    "evaluation/r2-p01-schnorr/p01model/independent.py",
    "evaluation/r2-p01-schnorr/p01model/interface.py",
    "evaluation/r2-p01-schnorr/p01model/provenance.py",
    "evaluation/r2-p01-schnorr/p01model/relations.py",
    "evaluation/r2-p01-schnorr/p01model/report.py",
    "evaluation/r2-p01-schnorr/p01model/semantic.py",
    "evaluation/r2-p01-schnorr/p01model/terms.py",
    RUNNER_PATH,
)

EXPECTED_QUERY_LENGTH = 448
EXPECTED_QUERY_SHA256 = (
    "ccb57bf733f23917e32f91edfefc8ff8"
    "2332bb30e36118f411f21caf874e4218"
)
EXPECTED_CHALLENGE_BYTE = 110
EXPECTED_CHALLENGE = 6


def _key_paths(value: Any, key: str, path: tuple[str, ...] = ()) -> list[tuple[str, ...]]:
    found: list[tuple[str, ...]] = []
    if isinstance(value, dict):
        for current_key, current_value in value.items():
            current_path = path + (current_key,)
            if current_key == key:
                found.append(current_path)
            found.extend(_key_paths(current_value, key, current_path))
    elif isinstance(value, list):
        for index, current_value in enumerate(value):
            found.extend(_key_paths(current_value, key, path + (str(index),)))
    return found


def _all_keys(value: Any) -> Iterator[str]:
    if isinstance(value, dict):
        for key, current_value in value.items():
            yield key
            yield from _all_keys(current_value)
    elif isinstance(value, list):
        for current_value in value:
            yield from _all_keys(current_value)


@contextmanager
def _copied_checkout() -> Iterator[tuple[Path, Path]]:
    with tempfile.TemporaryDirectory(prefix="p01-public-replay-") as temporary:
        temporary_root = Path(temporary)
        copied_root = temporary_root / "checkout"
        isolated_cwd = temporary_root / "isolated-cwd"
        isolated_cwd.mkdir(parents=True)
        for relative in COPY_ALLOWLIST:
            source = REPO_ROOT / relative
            destination = copied_root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        yield copied_root, isolated_cwd


def _write_expected(copied_root: Path, value: Any) -> None:
    (copied_root / EXPECTED_PATH).write_text(
        canonical_json_text(value, pretty=True),
        encoding="utf-8",
    )


def _run_copied(
    copied_root: Path,
    isolated_cwd: Path,
    *,
    requested_root: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    environment = {
        "PATH": os.environ.get("PATH", ""),
        "PYTHONPATH": "",
        "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    return subprocess.run(
        (
            sys.executable,
            str(copied_root / RUNNER_PATH),
            "--repo-root",
            str(copied_root if requested_root is None else requested_root),
            "--check",
        ),
        cwd=isolated_cwd,
        env=environment,
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )


class PublicReportConstructionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report(REPO_ROOT)
        cls.projection = expected_projection(cls.report)

    def test_build_strict_verify_and_canonical_json_round_trip(self) -> None:
        self.assertEqual(self.report["schema"], SCHEMA)
        rendered = canonical_json_text(self.report, pretty=True)
        decoded = load_bounded_json_bytes(rendered.encode("ascii"))

        self.assertEqual(decoded, self.report)
        self.assertEqual(canonical_json_bytes(decoded), canonical_json_bytes(self.report))
        # Strict verification re-identifies every typed lane and independently
        # rebuilds the complete report from the loaded checkout.
        self.assertEqual(verify_report(decoded, REPO_ROOT), [])

    def test_public_report_excludes_private_generation_material(self) -> None:
        encoded = canonical_json_bytes(self.report)
        private_raw = (REPO_ROOT / PRIVATE_SIDECAR_PATH).read_bytes()
        private_value = load_bounded_json_bytes(private_raw)
        private_artifact_id = str(artifact_content_id(private_raw)).encode("ascii")
        private_canonical_id = str(
            canonical_json_content_id(private_value)
        ).encode("ascii")

        self.assertNotIn(PRIVATE_SIDECAR_PATH.encode("ascii"), encoded)
        self.assertNotIn(b"private-generation.json", encoded)
        self.assertNotIn(private_artifact_id, encoded)
        self.assertNotIn(private_canonical_id, encoded)
        self.assertNotIn(b'"overall_pass"', encoded)
        self.assertEqual(_key_paths(self.report, "nonce"), [])

        for owner_local_type in (
            b"PrivateWitnessOccurrenceRef",
            b"SchnorrWitnessAssignment",
            b"CheckedRelationSatisfaction",
            b"OwnerLocalInvocationRef",
            b"OwnerLocalPrecommitmentHandle",
            b"ResponsePlan",
            b"LocalAccessReceipt",
            b"LocalGenerationRecord",
            b"LocalGenerationQualification",
        ):
            with self.subTest(owner_local_type=owner_local_type):
                self.assertNotIn(owner_local_type, encoded)

        # `scope.witness` names the P01 witness artifact; it is not a secret
        # scalar field. No other report object has a raw `witness` key.
        self.assertEqual(_key_paths(self.report, "witness"), [("scope", "witness")])
        self.assertIsInstance(self.report["scope"]["witness"], str)
        self.assertNotEqual(
            self.report["scope"]["witness"],
            private_value["witness"],
        )

        forbidden_private_keys = {
            "capability",
            "capability_id",
            "capability_ref",
            "local_binding",
            "local_binding_ref",
            "local_handle",
            "local_generation",
            "owner_generation",
            "private_binding",
            "private_binding_id",
            "private_capability",
            "private_access",
            "private_access_receipts",
            "private_body",
        }
        for key in _all_keys(self.report):
            with self.subTest(key=key):
                self.assertNotIn(key.lower(), forbidden_private_keys)

    def test_report_builder_has_no_expectation_oracle_parameter(self) -> None:
        signature = inspect.signature(build_report)
        self.assertEqual(tuple(signature.parameters), ("repo_root",))
        self.assertNotIn("expectations", signature.parameters)
        self.assertNotIn("expected", signature.parameters)
        with self.assertRaises(TypeError):
            build_report(REPO_ROOT, expectations={})  # type: ignore[call-arg]

    def test_exact_independent_query_and_disjoint_typed_identity_lanes(self) -> None:
        independent = self.report["independent_reconstruction"]
        query = bytes.fromhex(independent["query_hex"])
        receipt = self.report["public_executions"]["fiat_shamir"]["record"][
            "challenge_receipt"
        ]

        self.assertEqual(len(query), EXPECTED_QUERY_LENGTH)
        self.assertEqual(independent["query_byte_length"], EXPECTED_QUERY_LENGTH)
        self.assertEqual(hashlib.sha256(query).hexdigest(), EXPECTED_QUERY_SHA256)
        self.assertEqual(independent["query_sha256"], EXPECTED_QUERY_SHA256)
        self.assertEqual(independent["challenge_byte"], EXPECTED_CHALLENGE_BYTE)
        self.assertEqual(independent["challenge"], EXPECTED_CHALLENGE)
        self.assertEqual(receipt["query_hex"], independent["query_hex"])
        self.assertEqual(receipt["challenge"], EXPECTED_CHALLENGE)

        artifact_text = self.report["public_inputs"]["replay_fixture"][
            "artifact_content_id"
        ]
        validation_text = independent["validation_basis_id"]
        evidence_text = self.report["report_id"]
        artifact = ArtifactContentId.parse(artifact_text)
        validation = ValidationBasisId.parse(validation_text)
        evidence = EvidenceRecordId.parse(evidence_text)

        self.assertEqual(str(artifact).split(":", 1)[0], "sha256")
        self.assertEqual(
            str(validation).split(":", 1)[0], "validation-sha256"
        )
        self.assertEqual(str(evidence).split(":", 1)[0], "evidence-sha256")
        self.assertEqual(len({artifact.digest, validation.digest, evidence.digest}), 3)
        with self.assertRaises(ProvenanceError):
            ValidationBasisId.parse(artifact_text)
        with self.assertRaises(ProvenanceError):
            EvidenceRecordId.parse(validation_text)
        with self.assertRaises(ProvenanceError):
            ArtifactContentId.parse(evidence_text)

    def test_claim_bearing_fixture_fields_are_interpreted(self) -> None:
        fixture = load_public_fixture(
            REPO_ROOT,
            path=PUBLIC_INPUT_PATH,
            role="p01-public-replay-inputs",
        ).value
        self.assertNotIn("resource_limits", fixture)
        self.assertNotIn("finite_analysis_scope", fixture)
        self.assertEqual(fixture["disclosure"], "PublicPortableReplayInput")
        self.assertEqual(fixture["application_context"]["authority"], "Application")
        self.assertEqual(
            fixture["fresh_transcript"]["coin_source"],
            "FrozenPublicSupportPointNotSamplingEvidence",
        )

        plan = fixture["public_resource_plan"]
        contract = self.report["public_inputs"]["admitted_fixture_contract"]
        self.assertEqual(contract["public_resource_plan"], plan)
        self.assertEqual(contract["application_context_authority"], "Application")
        self.assertIn(
            "not evidence that a challenge was sampled",
            contract["fresh_challenge_source"]["non_claim"],
        )
        self.assertEqual(
            self.report["validation_bases"]["public-evaluator"]["hard_caps"],
            plan,
        )
        for realization in ("fresh", "fiat_shamir"):
            self.assertEqual(
                self.report["public_executions"][realization]["replay_request"][
                    "resources"
                ],
                plan,
            )

        derived = self.report["finite_analysis"]["derived_scope"]
        self.assertEqual(derived["authority"], "ExecutedFiniteAnalysisEvidence")
        self.assertEqual(
            derived["special_soundness"]["accepting_transcript_count"], 968
        )
        self.assertEqual(
            derived["special_soundness"][
                "unordered_distinct_challenge_fork_count"
            ],
            3388,
        )
        self.assertEqual(derived["shvzk"]["conditional_distribution_count"], 88)
        self.assertEqual(derived["shvzk"]["total_samples_per_side"], 968)

    def test_checked_in_expected_projection_is_the_post_build_oracle(self) -> None:
        expected = load_public_fixture(
            REPO_ROOT,
            path=EXPECTED_PATH,
            role="p01-expected-public-projection",
        ).value
        self.assertEqual(expected["schema"], EXPECTED_PROJECTION_SCHEMA)
        self.assertEqual(expected, self.projection)

    def test_public_gate_cases_cover_coin_and_resource_obligations(self) -> None:
        expected_results = {
            "semantic/public-coin-eligible.v3": (
                "Affirmative",
                "source-correspondence:public-coin-eligibility",
                "P01-PCOIN-OK",
            ),
            "negative/semantic/prover-owned-challenge.v3": (
                "SemanticNegative",
                "source-correspondence:public-coin-eligibility",
                "P01-PCOIN-001",
            ),
            "negative/execution/public-replay-resource-ceiling.v3": (
                "ResourceExceeded",
                "public-replay:resources",
                "P01-REPLAY-004",
            ),
            "negative/interface/proof-verification-resource-ceiling.v3": (
                "ResourceExceeded",
                "fs-proof-verification:resources",
                "P01-VERIFY-004",
            ),
            "negative/analysis/equal-challenge-fork.v3": (
                "SemanticNegative",
                "analysis:finite-special-soundness:distinct-challenges",
                "P01-SS-006",
            ),
        }
        self.assertEqual(len(self.report["cases"]), 45)
        for name, expected in expected_results.items():
            with self.subTest(case=name):
                case = self.report["cases"][name]
                self.assertEqual(
                    (case["outcome"], case["boundary"], case["code"]),
                    expected,
                )


class ReportPerturbationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report(REPO_ROOT)
        cls.projection = expected_projection(cls.report)

    def test_supplied_report_perturbation_fails_identity_and_exact_rebuild(self) -> None:
        mutated = copy.deepcopy(self.report)
        mutated["scope"]["disclosure"] = "perturbed-public-report"

        errors = verify_report(mutated, REPO_ROOT)
        self.assertIn("report evidence identity differs", errors)
        self.assertIn("exact public rebuild differs from the supplied report", errors)

    def test_oracle_mutation_does_not_rotate_rebuilt_report(self) -> None:
        with _copied_checkout() as (copied_root, isolated_cwd):
            mutated_oracle = copy.deepcopy(self.projection)
            mutated_oracle["report_id"] = "evidence-sha256:" + "00" * 32
            _write_expected(copied_root, mutated_oracle)

            completed = _run_copied(copied_root, isolated_cwd)
            self.assertEqual(completed.returncode, 1)
            rebuilt = load_bounded_json_bytes(completed.stdout.encode("ascii"))
            self.assertEqual(rebuilt, self.report)
            self.assertEqual(rebuilt["report_id"], self.report["report_id"])
            runner_error = load_bounded_json_bytes(
                completed.stderr.encode("ascii")
            )
            self.assertEqual(runner_error["error"]["kind"], "verification-failure")
            self.assertEqual(
                runner_error["error"]["detail"],
                ["post-build expected projection differs"],
            )

    def test_source_perturbations_rotate_report_and_fail_only_frozen_oracle(self) -> None:
        with _copied_checkout() as (copied_root, isolated_cwd):
            semantic_path = copied_root / (
                "evaluation/r2-p01-schnorr/p01model/semantic.py"
            )
            semantic_path.write_text(
                semantic_path.read_text(encoding="utf-8")
                + "\n# copied-checkout source perturbation\n",
                encoding="utf-8",
            )

            completed = _run_copied(copied_root, isolated_cwd)
            self.assertEqual(completed.returncode, 1)
            rebuilt = load_bounded_json_bytes(completed.stdout.encode("ascii"))
            self.assertNotEqual(rebuilt["report_id"], self.report["report_id"])
            self.assertNotEqual(expected_projection(rebuilt), self.projection)
            runner_error = load_bounded_json_bytes(completed.stderr.encode("ascii"))
            self.assertEqual(
                runner_error["error"]["detail"],
                ["post-build expected projection differs"],
            )
            self.assertNotEqual(
                rebuilt["validation_bases"]["semantic"]["id"],
                self.report["validation_bases"]["semantic"]["id"],
            )
            self.assertNotEqual(
                rebuilt["validation_bases"]["independent"]["id"],
                self.report["validation_bases"]["independent"]["id"],
            )
            self.assertEqual(
                rebuilt["independent_reconstruction"]["validation_basis_id"],
                rebuilt["validation_bases"]["independent"]["id"],
            )

        with _copied_checkout() as (copied_root, isolated_cwd):
            initializer_path = copied_root / (
                "evaluation/r2-p01-schnorr/p01model/__init__.py"
            )
            initializer_path.write_text(
                initializer_path.read_text(encoding="utf-8")
                + "\n# copied-checkout package-initializer perturbation\n",
                encoding="utf-8",
            )

            completed = _run_copied(copied_root, isolated_cwd)
            self.assertEqual(completed.returncode, 1)
            rebuilt = load_bounded_json_bytes(completed.stdout.encode("ascii"))
            self.assertNotEqual(rebuilt["report_id"], self.report["report_id"])
            self.assertNotEqual(expected_projection(rebuilt), self.projection)
            runner_error = load_bounded_json_bytes(completed.stderr.encode("ascii"))
            self.assertEqual(
                runner_error["error"]["detail"],
                ["post-build expected projection differs"],
            )
            self.assertEqual(
                set(rebuilt["validation_bases"]),
                set(self.report["validation_bases"]),
            )
            for component in sorted(self.report["validation_bases"]):
                with self.subTest(component=component):
                    self.assertNotEqual(
                        rebuilt["validation_bases"][component]["id"],
                        self.report["validation_bases"][component]["id"],
                    )

    def test_claim_bearing_fixture_mutations_are_refused(self) -> None:
        mutations = {
            "disclosure": "public-inputs.disclosure differs",
            "authority": "application_context.authority differs",
            "coin-source": "fresh_transcript.coin_source differs",
            "extra-top-key": "public-inputs fixture keys differ",
            "missing-top-key": "public-inputs fixture keys differ",
            "resource-shape": "public_resource_plan keys differ",
            "resource-budget": (
                "FS public qualification returned ResourceExceeded/P01-REPLAY-004"
            ),
            "analysis-scope-input": "public-inputs fixture keys differ",
            "non-claim-boundary": "non_claims differ",
        }
        for mutation, expected_detail in mutations.items():
            with self.subTest(mutation=mutation):
                with _copied_checkout() as (copied_root, isolated_cwd):
                    fixture_path = copied_root / PUBLIC_INPUT_PATH
                    fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
                    if mutation == "disclosure":
                        fixture["disclosure"] = "PerturbedPublicReplayInput"
                    elif mutation == "authority":
                        fixture["application_context"]["authority"] = (
                            "PublicEnvironment"
                        )
                    elif mutation == "coin-source":
                        fixture["fresh_transcript"]["coin_source"] = (
                            "SampledFreshChallenge"
                        )
                    elif mutation == "extra-top-key":
                        fixture["annotation"] = "identity-only"
                    elif mutation == "missing-top-key":
                        del fixture["fs_proof"]
                    elif mutation == "resource-shape":
                        fixture["public_resource_plan"]["max_private_reads"] = 2
                    elif mutation == "resource-budget":
                        fixture["public_resource_plan"]["max_hash_queries"] = 1
                    elif mutation == "analysis-scope-input":
                        fixture["finite_analysis_scope"] = {
                            "claim": "input-authored"
                        }
                    else:
                        fixture["non_claims"].append("arbitrary claim boundary")
                    fixture_path.write_text(
                        canonical_json_text(fixture, pretty=True),
                        encoding="utf-8",
                    )

                    completed = _run_copied(copied_root, isolated_cwd)
                    self.assertEqual(completed.returncode, 1)
                    self.assertEqual(completed.stdout, "")
                    runner_error = load_bounded_json_bytes(
                        completed.stderr.encode("ascii")
                    )
                    self.assertEqual(
                        runner_error["error"]["kind"], "runner-failure"
                    )
                    self.assertIsInstance(runner_error["error"]["detail"], str)
                    self.assertIn(
                        expected_detail,
                        runner_error["error"]["detail"],
                    )


class CopiedCheckoutReplayTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report(REPO_ROOT)
        cls.projection = expected_projection(cls.report)

    def test_minimal_allowlist_replays_with_isolated_cwd_and_pythonpath(self) -> None:
        self.assertNotIn(PRIVATE_SIDECAR_PATH, COPY_ALLOWLIST)
        with _copied_checkout() as (copied_root, isolated_cwd):
            copied_files = tuple(
                sorted(
                    path.relative_to(copied_root).as_posix()
                    for path in copied_root.rglob("*")
                    if path.is_file()
                )
            )
            self.assertEqual(copied_files, tuple(sorted(COPY_ALLOWLIST)))
            self.assertFalse((copied_root / PRIVATE_SIDECAR_PATH).exists())
            self.assertEqual(
                (copied_root / EXPECTED_PATH).read_bytes(),
                (REPO_ROOT / EXPECTED_PATH).read_bytes(),
            )

            completed = _run_copied(copied_root, isolated_cwd)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertEqual(completed.stderr, "")
            copied_report = load_bounded_json_bytes(
                completed.stdout.encode("ascii")
            )
            self.assertEqual(copied_report, self.report)

    def test_alternate_and_mixed_loaded_roots_are_refused(self) -> None:
        with tempfile.TemporaryDirectory(prefix="p01-alternate-root-") as alternate:
            with self.assertRaises(RootBindingError):
                build_report(Path(alternate))

        with _copied_checkout() as (copied_root, isolated_cwd):
            completed = _run_copied(
                copied_root,
                isolated_cwd,
                requested_root=REPO_ROOT,
            )
            self.assertEqual(completed.returncode, 1)
            self.assertEqual(completed.stdout, "")
            self.assertIn(
                "repository root differs from the checkout that loaded the evaluator",
                completed.stderr,
            )


if __name__ == "__main__":
    unittest.main()
