from __future__ import annotations

from dataclasses import replace
import copy
import json
from pathlib import Path
import tempfile
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(MODEL_ROOT))

from duplexmodel.diagnostics import MalformedInput, ProvenanceError  # noqa: E402
from duplexmodel.construction import (  # noqa: E402
    construction_id,
    core_id,
    parse_construction,
    protocol_id,
)
from duplexmodel.provenance import (  # noqa: E402
    assert_loaded_root,
    load_fixture,
    source_manifest,
    validation_basis_id,
)
from duplexmodel.report import (  # noqa: E402
    CONSTRUCTION_PATH,
    PUBLIC_INPUT_PATH,
    PUBLIC_PROOF_PATH,
    SOURCE_LEDGER_PATH,
    build_report,
    validate_source_ledger,
)
from duplexmodel.terms import artifact_id, load_json_bytes  # noqa: E402


class IdentityProvenanceTest(unittest.TestCase):
    def test_duplicate_json_keys_fail_closed(self) -> None:
        with self.assertRaisesRegex(MalformedInput, "duplicate JSON key"):
            load_json_bytes(b'{"schema":"a","schema":"b"}')

    def test_requested_root_must_equal_loaded_source_root(self) -> None:
        with tempfile.TemporaryDirectory(prefix="duplex-wrong-root-") as temporary:
            with self.assertRaisesRegex(ProvenanceError, "differs"):
                assert_loaded_root(Path(temporary))

    def test_public_source_manifest_excludes_tests_generation_and_private_data(self) -> None:
        manifest = source_manifest(REPO_ROOT)
        paths = {entry["path"] for entry in manifest}
        self.assertIn(
            "evaluation/duplex-sponge-transcript/duplexmodel/transition.py", paths
        )
        self.assertIn("evaluation/duplex-sponge-transcript/run.py", paths)
        self.assertTrue(all("/tests/" not in path for path in paths))
        self.assertNotIn("evaluation/duplex-sponge-transcript/generate.py", paths)
        self.assertTrue(all("private-generation" not in path for path in paths))

    def test_source_ledger_bytes_affect_validation_not_semantic_roots(self) -> None:
        bindings = tuple(
            load_fixture(REPO_ROOT, path, role=role)
            for path, role in (
                (CONSTRUCTION_PATH, "construction"),
                (PUBLIC_INPUT_PATH, "inputs"),
                (PUBLIC_PROOF_PATH, "proof"),
                (SOURCE_LEDGER_PATH, "ledger"),
            )
        )
        baseline = validation_basis_id(source_manifest(REPO_ROOT), bindings)
        changed_raw = bindings[-1].raw + b"\n"
        changed_ledger = replace(
            bindings[-1],
            raw=changed_raw,
            artifact_content_id=artifact_id(changed_raw),
        )
        changed = validation_basis_id(
            source_manifest(REPO_ROOT), bindings[:-1] + (changed_ledger,)
        )
        self.assertNotEqual(changed, baseline)
        report = build_report(REPO_ROOT)
        construction = parse_construction(bindings[0].value)
        self.assertEqual(
            report["semantic_roots"],
            {
                "core_id": core_id(construction.core),
                "construction_id": construction_id(construction),
                "fresh_protocol_id": protocol_id(construction, "Fresh"),
                "duplex_protocol_id": protocol_id(
                    construction, "DuplexSponge"
                ),
            },
        )

    def test_source_ledger_rejects_authority_and_malformed_digest_mutations(self) -> None:
        baseline = json.loads((REPO_ROOT / SOURCE_LEDGER_PATH).read_text())
        mutations = []
        digest = copy.deepcopy(baseline)
        digest["entries"][0]["sha256"] = "ABC"
        mutations.append(digest)
        authority = copy.deepcopy(baseline)
        authority["entries"][0]["status"] = "theorem-authority"
        mutations.append(authority)
        authenticated = copy.deepcopy(baseline)
        authenticated["fixture_boundary"]["source_authentication"] = True
        mutations.append(authenticated)
        extra_boundary = copy.deepcopy(baseline)
        extra_boundary["fixture_boundary"]["normative"] = True
        mutations.append(extra_boundary)
        for value in mutations:
            with self.subTest(value=value):
                with self.assertRaises(MalformedInput):
                    validate_source_ledger(value)

    def test_public_report_has_no_affirmative_security_case(self) -> None:
        report = build_report(REPO_ROOT)
        case = report["cases"]["analysis/security-nonpromotion"]
        self.assertEqual(case["outcome"], "CannotAnswer")
        self.assertNotIn("overall_pass", report)
        self.assertGreaterEqual(len(report["nonclaims"]), 8)

    def test_public_report_does_not_bind_private_generation_artifact(self) -> None:
        report = build_report(REPO_ROOT)
        private_path = REPO_ROOT / (
            "evaluation/duplex-sponge-transcript/cases/private-generation.json"
        )
        private_id = artifact_id(private_path.read_bytes())
        encoded = str(report).encode("utf-8")
        self.assertNotIn(b"private-generation.json", encoded)
        self.assertNotIn(private_id.encode("ascii"), encoded)
