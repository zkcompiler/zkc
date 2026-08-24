from __future__ import annotations

import hashlib
from pathlib import Path
import sys
import tempfile
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(MODEL_ROOT))

import p01model.diagnostics as diagnostics_module  # noqa: E402
import p01model.provenance as provenance_module  # noqa: E402
from p01model.diagnostics import (  # noqa: E402
    AFFIRMATIVE_CODES,
    CONSTRUCTIBLE_DRIVER_CODES,
    ENVIRONMENTAL_CODES,
    EXPLICIT_CLASSIFICATIONS,
    INTERNAL_INVARIANT_FAULT_CODES,
    RETIRED_DEAD_REDUNDANT_CODES,
    DiagnosticClass,
    DiagnosticContractError,
    classification_summary,
    scan_declared_codes,
)
from p01model.provenance import (  # noqa: E402
    ArtifactContentId,
    ContentMismatchError,
    EvidenceRecordId,
    JsonInputError,
    PathPolicyError,
    ProvenanceError,
    RootBindingError,
    SourceDeclaration,
    ValidationBasisId,
    artifact_content_id,
    bind_loaded_root,
    build_source_manifest,
    canonical_json_bytes,
    canonical_json_content_id,
    evidence_record_id,
    load_bounded_json_bytes,
    load_public_fixture,
    loaded_repo_root,
    safe_relative_path,
    validate_loaded_module,
    validate_source_manifest,
    validation_basis_id,
)


PROVENANCE_PATH = "evaluation/r2-p01-schnorr/p01model/provenance.py"
DIAGNOSTICS_PATH = "evaluation/r2-p01-schnorr/p01model/diagnostics.py"


class ProvenanceIdentityLaneTest(unittest.TestCase):
    def test_typed_identity_lanes_are_domain_separated_and_parse_exactly(self) -> None:
        preimage = {"component": "p01", "version": 1}
        raw = canonical_json_bytes(preimage)

        artifact = artifact_content_id(raw)
        validation = validation_basis_id("p01", preimage)
        evidence = evidence_record_id("p01", preimage)

        self.assertIsInstance(artifact, ArtifactContentId)
        self.assertIsInstance(validation, ValidationBasisId)
        self.assertIsInstance(evidence, EvidenceRecordId)
        self.assertEqual(artifact.digest, hashlib.sha256(raw).hexdigest())
        self.assertEqual(ArtifactContentId.parse(str(artifact)), artifact)
        self.assertEqual(ValidationBasisId.parse(str(validation)), validation)
        self.assertEqual(EvidenceRecordId.parse(str(evidence)), evidence)
        self.assertEqual(validation_basis_id("p01", preimage), validation)
        self.assertEqual(evidence_record_id("p01", preimage), evidence)

        self.assertEqual(str(artifact).split(":", 1)[0], "sha256")
        self.assertEqual(str(validation).split(":", 1)[0], "validation-sha256")
        self.assertEqual(str(evidence).split(":", 1)[0], "evidence-sha256")
        self.assertEqual(len({artifact.digest, validation.digest, evidence.digest}), 3)

        with self.assertRaises(ProvenanceError):
            ValidationBasisId.parse(str(artifact))
        with self.assertRaises(ProvenanceError):
            EvidenceRecordId.parse(str(validation))
        with self.assertRaises(ProvenanceError):
            ArtifactContentId.parse(str(evidence))
        with self.assertRaises(ProvenanceError):
            ArtifactContentId.parse("sha256:" + "A" * 64)


class SourceManifestTest(unittest.TestCase):
    def test_manifest_is_canonical_and_binds_loaded_modules_and_root(self) -> None:
        self.assertEqual(loaded_repo_root(), REPO_ROOT)
        self.assertEqual(bind_loaded_root(REPO_ROOT), REPO_ROOT)

        declarations = (
            SourceDeclaration(
                "semantic-provenance",
                PROVENANCE_PATH,
                provenance_module,
            ),
            SourceDeclaration(
                "diagnostic-taxonomy",
                DIAGNOSTICS_PATH,
                diagnostics_module,
            ),
        )
        manifest = build_source_manifest(
            REPO_ROOT,
            component="p01-phase-b",
            declarations=reversed(declarations),
        )
        rebuilt = build_source_manifest(
            REPO_ROOT,
            component="p01-phase-b",
            declarations=declarations,
        )

        self.assertEqual(manifest, rebuilt)
        self.assertEqual(manifest.identity, rebuilt.identity)
        self.assertEqual(
            manifest.entries,
            tuple(sorted(manifest.entries, key=lambda item: (item.role, item.path))),
        )
        self.assertEqual(
            [entry.role for entry in manifest.entries],
            ["diagnostic-taxonomy", "semantic-provenance"],
        )
        self.assertIsInstance(manifest.identity, ValidationBasisId)

        validate_source_manifest(
            manifest,
            REPO_ROOT,
            loaded_modules={
                PROVENANCE_PATH: provenance_module,
                DIAGNOSTICS_PATH: diagnostics_module,
            },
        )
        validate_loaded_module(
            REPO_ROOT,
            path=PROVENANCE_PATH,
            module=provenance_module,
        )
        with self.assertRaises(ContentMismatchError):
            validate_loaded_module(
                REPO_ROOT,
                path=DIAGNOSTICS_PATH,
                module=provenance_module,
            )

    def test_current_byte_mismatch_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(
            prefix=".p01-provenance-mismatch-",
            dir=REPO_ROOT,
        ) as temporary:
            source = Path(temporary) / "source.py"
            source.write_bytes(b"value = 1\n")
            relative = source.relative_to(REPO_ROOT).as_posix()
            manifest = build_source_manifest(
                REPO_ROOT,
                component="p01-byte-mismatch",
                declarations=(SourceDeclaration("evaluator", relative),),
            )
            source.write_bytes(b"value = 2\n")

            with self.assertRaises(ContentMismatchError):
                validate_source_manifest(manifest, REPO_ROOT)

    def test_path_symlink_and_alternate_root_are_rejected(self) -> None:
        traversal_cases = (
            "../outside.py",
            "evaluation/../outside.py",
            "/absolute/source.py",
            "evaluation\\source.py",
        )
        for candidate in traversal_cases:
            with self.subTest(candidate=candidate):
                with self.assertRaises(PathPolicyError):
                    safe_relative_path(candidate)

        with tempfile.TemporaryDirectory(
            prefix=".p01-provenance-symlink-",
            dir=REPO_ROOT,
        ) as temporary:
            link = Path(temporary) / "linked-source.py"
            try:
                link.symlink_to(REPO_ROOT / PROVENANCE_PATH)
            except OSError as error:
                self.skipTest(f"symlink creation is unavailable: {error}")
            relative = link.relative_to(REPO_ROOT).as_posix()
            with self.assertRaises(PathPolicyError):
                build_source_manifest(
                    REPO_ROOT,
                    component="p01-symlink-rejection",
                    declarations=(SourceDeclaration("evaluator", relative),),
                )

        with tempfile.TemporaryDirectory(prefix="p01-alternate-root-") as alternate:
            with self.assertRaises(RootBindingError):
                bind_loaded_root(Path(alternate))


class PublicJsonFixtureTest(unittest.TestCase):
    def test_bounded_json_rejects_duplicate_keys_floats_and_oversize(self) -> None:
        rejected = (
            b'{"duplicate":1,"duplicate":2}',
            b'{"float":1.25}',
            b'{"not_finite":NaN}',
        )
        for raw in rejected:
            with self.subTest(raw=raw):
                with self.assertRaises(JsonInputError):
                    load_bounded_json_bytes(raw)

        with self.assertRaises(JsonInputError):
            load_bounded_json_bytes(b"{}", maximum=1)
        with self.assertRaises(JsonInputError):
            canonical_json_bytes({"float": 1.25})

        self.assertEqual(
            load_bounded_json_bytes(b'{"z":[2,1],"a":true}'),
            {"a": True, "z": [2, 1]},
        )

    def test_public_fixture_binds_exact_bytes_and_canonical_value_separately(
        self,
    ) -> None:
        first_raw = b'{\n  "z": [2, 1],\n  "a": true\n}\n'
        second_raw = b'{"a":true,"z":[2,1]}'
        normalized = {"a": True, "z": [2, 1]}

        with tempfile.TemporaryDirectory(
            prefix=".p01-public-fixture-",
            dir=REPO_ROOT,
        ) as temporary:
            first_path = Path(temporary) / "first.json"
            second_path = Path(temporary) / "second.json"
            first_path.write_bytes(first_raw)
            second_path.write_bytes(second_raw)
            first_relative = first_path.relative_to(REPO_ROOT).as_posix()
            second_relative = second_path.relative_to(REPO_ROOT).as_posix()

            first = load_public_fixture(REPO_ROOT, path=first_relative)
            second = load_public_fixture(REPO_ROOT, path=second_relative)

            self.assertEqual(first.value, normalized)
            self.assertEqual(second.value, normalized)
            self.assertEqual(first.artifact_id, artifact_content_id(first_raw))
            self.assertEqual(second.artifact_id, artifact_content_id(second_raw))
            self.assertNotEqual(first.artifact_id, second.artifact_id)
            self.assertEqual(
                first.canonical_json_id,
                canonical_json_content_id(normalized),
            )
            self.assertEqual(first.canonical_json_id, second.canonical_json_id)
            self.assertEqual(
                load_public_fixture(
                    REPO_ROOT,
                    path=first_relative,
                    expected_artifact_id=first.artifact_id,
                ),
                first,
            )
            self.assertEqual(
                first.term()["artifact_content_id"],
                str(artifact_content_id(first_raw)),
            )
            self.assertEqual(
                first.term()["canonical_json_content_id"],
                str(canonical_json_content_id(normalized)),
            )

            with self.assertRaises(ContentMismatchError):
                load_public_fixture(
                    REPO_ROOT,
                    path=first_relative,
                    expected_artifact_id=artifact_content_id(b"different bytes"),
                )


class DiagnosticClosureTest(unittest.TestCase):
    EXPECTED_COUNTS = {
        DiagnosticClass.AFFIRMATIVE: 30,
        DiagnosticClass.CONSTRUCTIBLE_DRIVER: 144,
        DiagnosticClass.INTERNAL_INVARIANT_FAULT: 15,
        DiagnosticClass.ENVIRONMENTAL: 1,
        DiagnosticClass.RETIRED_DEAD_REDUNDANT: 13,
    }

    def test_current_source_closure_is_exact_unique_and_deterministic(self) -> None:
        first = classification_summary()
        second = classification_summary()
        scanned = scan_declared_codes()
        category_sets = (
            AFFIRMATIVE_CODES,
            CONSTRUCTIBLE_DRIVER_CODES,
            INTERNAL_INVARIANT_FAULT_CODES,
            ENVIRONMENTAL_CODES,
            RETIRED_DEAD_REDUNDANT_CODES,
        )

        self.assertEqual(first, second)
        self.assertEqual(first.term(), second.term())
        self.assertEqual(first.declared_count, 203)
        self.assertEqual(dict(first.counts), self.EXPECTED_COUNTS)
        self.assertEqual(sum(self.EXPECTED_COUNTS.values()), first.declared_count)
        self.assertEqual(set(scanned), set(EXPLICIT_CLASSIFICATIONS))
        self.assertEqual(
            len(EXPLICIT_CLASSIFICATIONS),
            sum(len(codes) for codes in category_sets),
        )
        self.assertEqual(
            [declaration.code for declaration in first.declarations],
            sorted(scanned),
        )
        self.assertEqual(
            first.source_files,
            tuple(sorted(first.source_files)),
        )
        self.assertTrue(all(len(owners) == 1 for owners in scanned.values()))
        self.assertEqual(
            first.term()["coverage_semantics"],
            "classification closure only; it is not diagnostic reachability "
            "or executed-driver coverage",
        )

    def test_synthetic_unknown_and_stale_closure_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory(prefix="p01-diagnostic-closure-") as temporary:
            source = Path(temporary) / "unknown.py"
            source.write_text(
                'DIAGNOSTIC = "P01-UNKNOWN-999"\n',
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                DiagnosticContractError,
                r"unknown=P01-UNKNOWN-999.*stale=",
            ):
                classification_summary(Path(temporary))


if __name__ == "__main__":
    unittest.main()
