"""Tests for strict, typed, and offline constructive-source provenance."""

from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import friiormodel.provenance as provenance_module  # noqa: E402
from friiormodel.provenance import (  # noqa: E402
    ArtifactContentId,
    CanonicalContentId,
    IMPLEMENTATION_SNAPSHOT_FILE_COUNTS,
    MAX_LEDGER_BYTES,
    PAPER_IDS,
    SOURCE_LEDGER_SCOPE,
    ValidationBasisId,
    artifact_content_id,
    canonical_content_id,
    check_source_ledger,
    load_bounded_json_bytes,
    load_source_ledger,
    load_source_ledger_bytes,
    validation_basis_id,
)
from friiormodel.terms import ModelFailure, OutcomeClass, SemanticId  # noqa: E402


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
LEDGER_PATH = PACKAGE_ROOT / "cases" / "source-ledger.json"

EXPECTED_LEDGER_ARTIFACT_ID = (
    "sha256:a767b8ba1526d86b2214f6b4127065e4d3707a6d1c43e76a965d71c222da42b4"
)
EXPECTED_LEDGER_CANONICAL_ID = (
    "canonical-sha256:"
    "b0240e40602156ead345260d442a263a0d9fa2e299c027a34c11ae59bed9624c"
)

EXPECTED_PAPERS = {
    "bcs-iop-2016-116-r2": (
        "a2dc9bd042665081664287281b9bcf64735be2c818ce9207cce57cc43939fa2f",
        3_809_663,
    ),
    "eccc-fri-tr17-134-r2": (
        "f9868a06d50c727b349516d54915aa2a9bf8d966d8b04597bce054db73c1294d",
        1_140_342,
    ),
    "ethstark-2021-582-r3": (
        "23b1bd72be468c3b1781bfd76c075a843bb529e8dedc763629c67a080b4f0099",
        994_149,
    ),
    "fri-fs-2023-1071-r7": (
        "bb7a7e87b9000c98106de99c9af9d289def2a1b91919a3507ee78bf9bfd16947",
        995_671,
    ),
    "icalp-fri-2018-14": (
        "e244896fb6e7fcab7fe4de00e31a36003b941b6550e062fdb5ee66d78641498d",
        562_655,
    ),
}

EXPECTED_SNAPSHOTS = {
    "plonky3-3da3467-fri-profile": {
        "repository": "https://github.com/Plonky3/Plonky3.git",
        "commit": "3da346791c813433b201299afc3d10bf42f8a078",
        "tree": "3e9f4076ca8cd681a6d4358ffee1fbb13edf96e7",
        "files": (
            (
                "challenger/src/grinding_challenger.rs",
                "6b95acf31840bd00e034036ec1c7cb98ae1fd48e62620bfab9bc9b689e9dae5e",
                14_406,
            ),
            (
                "challenger/src/serializing_challenger.rs",
                "030810da51b53889316a47aac6378cfe6f8a32978e004f883c8ab9e5804e8fca",
                17_895,
            ),
            (
                "commit/src/mmcs.rs",
                "d723314212fd4cc1f836d824255183d80cfbfa682ae858667fefb6ade1c0a206",
                12_880,
            ),
            (
                "fri/src/config.rs",
                "9b4eddc05aff09c5a3530ef3806e5164397c8da154a5fa9ec8440ad8c73b0d06",
                8_308,
            ),
            (
                "fri/src/proof.rs",
                "5b753fa3abf9a0189ee6534b1dcca09649c771ef6f359dfbf9d2e61bd1fa5e3a",
                2_955,
            ),
            (
                "fri/src/prover.rs",
                "88f7bec4b2e21753f03e3b4d17250e592a3ad9c195237c79089e883109102ac7",
                18_261,
            ),
            (
                "fri/src/two_adic_pcs.rs",
                "318e76ddb6e51c04bed4344f4a88307f2491f9d5472e6c876ec5db43958b84ca",
                35_603,
            ),
            (
                "fri/src/verifier.rs",
                "2d406ef747eeacc1b250be58fe07c0eaa7c882593604ce797841481a2ca8a453",
                87_462,
            ),
            (
                "merkle-tree/src/hiding_mmcs.rs",
                "fe19d4a894a4878ed42647c73598c30d7521f820deb8ffb8ec6e6a54d6059c16",
                16_550,
            ),
            (
                "merkle-tree/src/mmcs/batch.rs",
                "e91228643f1d5a48c683c94cfa5fc9d75212c6b64e64d9d93c51b6c7525d713a",
                38_265,
            ),
            (
                "merkle-tree/src/mmcs/mod.rs",
                "c6af51fcae2dd8a2709f6b17cad2356b6f441203a9a06955d37cc5a5c2216db4",
                34_868,
            ),
            (
                "merkle-tree/src/pruning.rs",
                "acbad34851adaf33da0713fa158d345c035a4eefeec6995a384f6ac6c610d522",
                25_444,
            ),
        ),
    },
    "winterfell-2f78ee9-fri-profile": {
        "repository": "https://github.com/facebook/winterfell.git",
        "commit": "2f78ee9bf667a561bdfcdfa68668d0f9b18b8315",
        "tree": "617fe80a8920aeb4f381d22fe2b71159d5c8667d",
        "files": (
            (
                "crypto/src/commitment.rs",
                "280d313081cedaa4e04f6b60d858bdff5d4216e44346837aa174235de9de0993",
                3_507,
            ),
            (
                "crypto/src/hash/blake/mod.rs",
                "dea12c3b59b053ac5baea3cf062b84effd7d42277fab7d814854931a65041a47",
                5_033,
            ),
            (
                "crypto/src/merkle/mod.rs",
                "045e3ae26327cc5c5c53bf1586b7c4c1aea76c83000497cd7ae38de195eeaa29",
                15_463,
            ),
            (
                "crypto/src/merkle/proofs.rs",
                "5809e4cab3e344229df65bbdc54404623c2ca2ba24cac63e44c101cf6550afe7",
                17_801,
            ),
            (
                "crypto/src/random/default.rs",
                "356866fc0db872c0346b0561ac5a13f061ad3c228f4b2660d2301181c8cebd79",
                9_611,
            ),
            (
                "fri/src/folding/mod.rs",
                "d77d2a102f1568566d909b6b4aaa6e3ef5250e7c649d30b517fcf5538960cbcf",
                8_210,
            ),
            (
                "fri/src/options.rs",
                "86ef869c2b32aa56bddd10949c3beea325c95470cbd771e6e79cd17eee6f86fc",
                3_447,
            ),
            (
                "fri/src/proof.rs",
                "1acc906052c8bb7cc0d2ac544db0015d9bfafed437badd382244e0e05f720848",
                14_840,
            ),
            (
                "fri/src/prover/channel.rs",
                "69cdd9a38bc1d590221eb89aa14b1ea7f1b05c810bc918640a2cbbdc8befe060",
                5_477,
            ),
            (
                "fri/src/prover/mod.rs",
                "b5a8fbc8ce577094fea4cb3d14dac5da6a2104828fca34a9886f68e928d659c7",
                15_675,
            ),
            (
                "fri/src/utils.rs",
                "072ef38d36e51b6d276218665f37fd4d74069c864da03a1c7199e5f556d8f96b",
                1_106,
            ),
            (
                "fri/src/verifier/channel.rs",
                "8e67a94589c6b4ffb5162c9772aa8c53f76fda65bf18b0a047af7e61839d1e11",
                7_835,
            ),
            (
                "fri/src/verifier/mod.rs",
                "cdffd26693169a0283a0df2e58db303f67fec057d753d6ff546a1594ea583378",
                16_061,
            ),
            (
                "prover/src/channel.rs",
                "9f3ba32d696ee9b3dd60c37018f826e1a2d66b7125e27372a083e1060d0e1547",
                8_786,
            ),
            (
                "prover/src/lib.rs",
                "efadfdf7b156af1db1f5a169b62587acb646b2994e3e5a28aa1a3088af4ca949",
                24_693,
            ),
            (
                "verifier/src/lib.rs",
                "5b3acf2d230be7e646af39a55ce25ab3c5a6bd4412ea6a76f2107b7972f71407",
                17_215,
            ),
            (
                "winterfell/src/lib.rs",
                "2e11f000097ef46db358dca0f12de835e35469c255ce3ad044082596e26493f8",
                28_546,
            ),
        ),
    },
}


def _render(value: dict[str, object]) -> bytes:
    return (json.dumps(value, ensure_ascii=True, indent=2) + "\n").encode("ascii")


class SourceLedgerFixtureTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.raw = LEDGER_PATH.read_bytes()
        cls.ledger = load_source_ledger(LEDGER_PATH)

    def test_fixture_has_exact_constructive_scope_and_frozen_identity(self) -> None:
        self.assertEqual(self.ledger.normalized_value["scope"], SOURCE_LEDGER_SCOPE)
        self.assertEqual(str(self.ledger.artifact_id), EXPECTED_LEDGER_ARTIFACT_ID)
        self.assertEqual(str(self.ledger.canonical_id), EXPECTED_LEDGER_CANONICAL_ID)
        self.assertEqual(self.ledger.exact_bytes, self.raw)
        self.assertEqual(
            self.ledger.canonical_id,
            canonical_content_id(self.ledger.normalized_value),
        )

    def test_exact_five_primary_paper_artifacts_are_frozen(self) -> None:
        self.assertEqual(tuple(EXPECTED_PAPERS), PAPER_IDS)
        actual = {
            paper.identifier: (paper.artifact_content_id.digest, paper.byte_length)
            for paper in self.ledger.papers
        }
        self.assertEqual(actual, EXPECTED_PAPERS)

    def test_exact_implementation_manifests_are_frozen(self) -> None:
        self.assertEqual(
            IMPLEMENTATION_SNAPSHOT_FILE_COUNTS,
            {identifier: len(entry["files"]) for identifier, entry in EXPECTED_SNAPSHOTS.items()},
        )
        for snapshot in self.ledger.implementation_snapshots:
            with self.subTest(snapshot=snapshot.identifier):
                expected = EXPECTED_SNAPSHOTS[snapshot.identifier]
                self.assertEqual(snapshot.repository_url, expected["repository"])
                self.assertEqual(snapshot.commit, expected["commit"])
                self.assertEqual(snapshot.tree, expected["tree"])
                actual_files = tuple(
                    (source.path, source.artifact_content_id.digest, source.byte_length)
                    for source in snapshot.selected_files
                )
                self.assertEqual(actual_files, expected["files"])

    def test_revision_metadata_and_profile_constraints_are_retained(self) -> None:
        snapshots = {
            entry["id"]: entry
            for entry in self.ledger.normalized_value["implementation_snapshots"]
        }
        self.assertEqual(
            snapshots["plonky3-3da3467-fri-profile"]["revision"],
            {
                "object_format": "sha1",
                "commit": "3da346791c813433b201299afc3d10bf42f8a078",
                "tree": "3e9f4076ca8cd681a6d4358ffee1fbb13edf96e7",
                "committer_date": "2026-07-13T11:42:11+04:00",
                "subject": "Fix BCHKS25 theorem citation (#1948)",
            },
        )
        winterfell = snapshots["winterfell-2f78ee9-fri-profile"]
        constraints = " ".join(winterfell["interpretation_constraints"])
        self.assertIn("selected comparison profile", constraints)
        self.assertIn("surrounding STARK seam", constraints)

    def test_analysis_only_sources_are_explicit_exclusions_not_paper_entries(self) -> None:
        paper_ids = {paper.identifier for paper in self.ledger.papers}
        self.assertNotIn("afk-multi-round-fs-2021-1377-v2", paper_ids)
        self.assertNotIn("block-tiwari-concrete-fri-2024-1161", paper_ids)
        exclusions = " ".join(
            self.ledger.normalized_value["claim_boundary"][
                "excluded_from_this_ledger"
            ]
        )
        for name in ("AFK", "Concrete FRI", "DEEP-FRI", "STIR", "WHIR"):
            self.assertIn(name, exclusions)

    def test_binding_term_contains_value_and_both_distinct_content_ids(self) -> None:
        binding = self.ledger.binding_term()
        self.assertEqual(binding["scope"], SOURCE_LEDGER_SCOPE)
        self.assertEqual(binding["value"], self.ledger.normalized_value)
        self.assertEqual(binding["artifact_content_id"], str(self.ledger.artifact_id))
        self.assertEqual(binding["canonical_content_id"], str(self.ledger.canonical_id))
        self.assertNotEqual(
            binding["artifact_content_id"],
            binding["canonical_content_id"],
        )

    def test_normalized_value_is_a_defensive_copy(self) -> None:
        first = self.ledger.normalized_value
        first["scope"] = "changed"
        self.assertEqual(self.ledger.normalized_value["scope"], SOURCE_LEDGER_SCOPE)


class ProvenanceIdentityTest(unittest.TestCase):
    def test_identity_carriers_are_disjoint_from_each_other_and_semantic_id(self) -> None:
        digest = "12" * 32
        artifact = ArtifactContentId(digest)
        canonical = CanonicalContentId(digest)
        validation = ValidationBasisId(digest)
        self.assertNotEqual(artifact, canonical)
        self.assertNotEqual(artifact, validation)
        self.assertNotEqual(canonical, validation)
        for value in (artifact, canonical, validation):
            self.assertNotIsInstance(value, SemanticId)
        self.assertEqual(str(artifact), f"sha256:{digest}")
        self.assertEqual(str(canonical), f"canonical-sha256:{digest}")
        self.assertEqual(str(validation), f"validation-sha256:{digest}")

    def test_identity_parsers_do_not_cast_between_lanes(self) -> None:
        digest = "ab" * 32
        artifact = ArtifactContentId(digest)
        canonical = CanonicalContentId(digest)
        validation = ValidationBasisId(digest)
        self.assertEqual(ArtifactContentId.parse(str(artifact)), artifact)
        self.assertEqual(CanonicalContentId.parse(str(canonical)), canonical)
        self.assertEqual(ValidationBasisId.parse(str(validation)), validation)
        for parser, wrong in (
            (ArtifactContentId.parse, str(canonical)),
            (CanonicalContentId.parse, str(artifact)),
            (ValidationBasisId.parse, str(artifact)),
        ):
            with self.subTest(parser=parser.__qualname__), self.assertRaises(
                ModelFailure
            ) as raised:
                parser(wrong)
            self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)

    def test_validation_basis_is_domain_separated_and_deterministic(self) -> None:
        preimage = {"sources": [{"path": "verify.py", "sha256": "00" * 32}]}
        first = validation_basis_id("public-verifier", preimage)
        self.assertEqual(first, validation_basis_id("public-verifier", preimage))
        self.assertNotEqual(first, validation_basis_id("report-builder", preimage))
        self.assertIsInstance(first, ValidationBasisId)
        self.assertNotEqual(first.digest, canonical_content_id(preimage).digest)


class StrictLoadingTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.raw = LEDGER_PATH.read_bytes()
        cls.value = load_source_ledger_bytes(cls.raw).normalized_value

    def _failure_for(self, raw: bytes) -> ModelFailure:
        with self.assertRaises(ModelFailure) as raised:
            load_source_ledger_bytes(raw)
        return raised.exception

    def test_whitespace_changes_artifact_id_but_not_canonical_id(self) -> None:
        original = load_source_ledger_bytes(self.raw)
        changed = load_source_ledger_bytes(b"\n \t" + self.raw)
        self.assertNotEqual(original.artifact_id, changed.artifact_id)
        self.assertEqual(original.canonical_id, changed.canonical_id)

    def test_semantic_mutation_changes_both_content_id_lanes(self) -> None:
        original = load_source_ledger_bytes(self.raw)
        value = deepcopy(self.value)
        current = value["papers"][0]["content"]["artifact_content_id"]
        replacement = "0" if current[-1] != "0" else "1"
        value["papers"][0]["content"]["artifact_content_id"] = (
            current[:-1] + replacement
        )
        changed = load_source_ledger_bytes(_render(value))
        self.assertNotEqual(original.artifact_id, changed.artifact_id)
        self.assertNotEqual(original.canonical_id, changed.canonical_id)

    def test_duplicate_keys_floats_and_reordered_keys_are_malformed(self) -> None:
        duplicate = self.raw.replace(
            b'{\n  "schema":',
            b'{\n  "schema": "zkc.native-fri-ior.source-ledger.v1",\n  "schema":',
            1,
        )
        duplicate_failure = self._failure_for(duplicate)
        self.assertEqual(duplicate_failure.code, "FRI-IOR-PROVENANCE-011")

        floating = self.raw.replace(b'"byte_length": 3809663', b'"byte_length": 1.5', 1)
        float_failure = self._failure_for(floating)
        self.assertEqual(float_failure.code, "FRI-IOR-PROVENANCE-008")

        reordered_value = {
            key: self.value[key]
            for key in reversed(tuple(self.value))
        }
        reorder_failure = self._failure_for(_render(reordered_value))
        self.assertEqual(reorder_failure.code, "FRI-IOR-PROVENANCE-024")

    def test_unknown_and_missing_keys_are_malformed(self) -> None:
        extra = deepcopy(self.value)
        extra["extra"] = False
        self.assertEqual(
            self._failure_for(_render(extra)).code,
            "FRI-IOR-PROVENANCE-024",
        )
        missing = deepcopy(self.value)
        del missing["claim_boundary"]
        self.assertEqual(
            self._failure_for(_render(missing)).code,
            "FRI-IOR-PROVENANCE-024",
        )

    def test_schema_scope_and_git_object_format_are_unsupported(self) -> None:
        for path, replacement, code in (
            (("schema",), "zkc.native-fri-ior.source-ledger.v2", "047"),
            (("scope",), "complete-theorem-corpus", "048"),
            (
                ("implementation_snapshots", 0, "revision", "object_format"),
                "sha256",
                "042",
            ),
        ):
            value = deepcopy(self.value)
            target = value
            for part in path[:-1]:
                target = target[part]
            target[path[-1]] = replacement
            failure = self._failure_for(_render(value))
            self.assertIs(failure.outcome, OutcomeClass.UNSUPPORTED)
            self.assertEqual(failure.code, f"FRI-IOR-PROVENANCE-{code}")

    def test_ids_paths_urls_and_array_order_are_strict(self) -> None:
        uppercase = deepcopy(self.value)
        digest = uppercase["papers"][0]["content"]["artifact_content_id"]
        uppercase["papers"][0]["content"]["artifact_content_id"] = (
            "sha256:" + digest.removeprefix("sha256:").upper()
        )
        self.assertEqual(
            self._failure_for(_render(uppercase)).code,
            "FRI-IOR-PROVENANCE-001",
        )

        insecure = deepcopy(self.value)
        insecure["papers"][0]["landing_url"] = "http://eprint.iacr.org/2016/116"
        self.assertEqual(
            self._failure_for(_render(insecure)).code,
            "FRI-IOR-PROVENANCE-031",
        )

        local = deepcopy(self.value)
        local["implementation_snapshots"][0]["selected_files"][0]["path"] = (
            "/tmp/source.rs"
        )
        self.assertEqual(
            self._failure_for(_render(local)).code,
            "FRI-IOR-PROVENANCE-038",
        )

        unsorted_papers = deepcopy(self.value)
        unsorted_papers["papers"][0], unsorted_papers["papers"][1] = (
            unsorted_papers["papers"][1],
            unsorted_papers["papers"][0],
        )
        self.assertEqual(
            self._failure_for(_render(unsorted_papers)).code,
            "FRI-IOR-PROVENANCE-050",
        )

        unsorted_paths = deepcopy(self.value)
        files = unsorted_paths["implementation_snapshots"][0]["selected_files"]
        files[0], files[1] = files[1], files[0]
        self.assertEqual(
            self._failure_for(_render(unsorted_paths)).code,
            "FRI-IOR-PROVENANCE-045",
        )

    def test_expected_artifact_binding_refuses_mismatch_and_wrong_id_kind(self) -> None:
        actual = artifact_content_id(self.raw)
        self.assertEqual(
            load_source_ledger_bytes(self.raw, expected_artifact_id=actual).artifact_id,
            actual,
        )
        with self.assertRaises(ModelFailure) as mismatch:
            load_source_ledger_bytes(
                self.raw,
                expected_artifact_id=ArtifactContentId("00" * 32),
            )
        self.assertIs(mismatch.exception.outcome, OutcomeClass.REFUSED)
        self.assertEqual(mismatch.exception.code, "FRI-IOR-PROVENANCE-055")

        with self.assertRaises(ModelFailure) as wrong_kind:
            load_source_ledger_bytes(
                self.raw,
                expected_artifact_id=CanonicalContentId(actual.digest),  # type: ignore[arg-type]
            )
        self.assertIs(wrong_kind.exception.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(wrong_kind.exception.code, "FRI-IOR-PROVENANCE-054")

    def test_input_bound_is_a_deterministic_limit(self) -> None:
        with self.assertRaises(ModelFailure) as raised:
            load_bounded_json_bytes(b" " * (MAX_LEDGER_BYTES + 1))
        self.assertIs(
            raised.exception.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(raised.exception.code, "FRI-IOR-PROVENANCE-018")


class OfflineAndDiagnosticTest(unittest.TestCase):
    def test_normal_load_is_network_free(self) -> None:
        with mock.patch(
            "urllib.request.urlopen",
            side_effect=AssertionError("network access is forbidden"),
        ), mock.patch(
            "socket.create_connection",
            side_effect=AssertionError("network access is forbidden"),
        ):
            ledger = load_source_ledger(LEDGER_PATH)
        self.assertEqual(len(ledger.papers), 5)

    def test_check_surface_uses_the_full_stable_outcome_partition(self) -> None:
        observed = {check_source_ledger(LEDGER_PATH).outcome}

        value = load_source_ledger(LEDGER_PATH).normalized_value
        unsupported = deepcopy(value)
        unsupported["scope"] = "complete-theorem-corpus"
        malformed = b'{"duplicate":1,"duplicate":2}'

        with tempfile.TemporaryDirectory(prefix="fri-ior-provenance-") as directory:
            root = Path(directory)
            unsupported_path = root / "unsupported.json"
            unsupported_path.write_bytes(_render(unsupported))
            malformed_path = root / "malformed.json"
            malformed_path.write_bytes(malformed)
            large_path = root / "large.json"
            large_path.write_bytes(b" " * (MAX_LEDGER_BYTES + 1))

            observed.add(check_source_ledger(unsupported_path).outcome)
            observed.add(check_source_ledger(root / "missing.json").outcome)
            observed.add(check_source_ledger(malformed_path).outcome)
            observed.add(check_source_ledger(large_path).outcome)
            observed.add(
                check_source_ledger(
                    LEDGER_PATH,
                    expected_artifact_id=ArtifactContentId("00" * 32),
                ).outcome
            )
            observed.add(
                check_source_ledger(
                    LEDGER_PATH,
                    expected_artifact_id=CanonicalContentId("00" * 32),  # type: ignore[arg-type]
                ).outcome
            )

        with mock.patch.object(
            provenance_module,
            "load_source_ledger",
            side_effect=RuntimeError("injected evaluator defect"),
        ):
            observed.add(check_source_ledger(LEDGER_PATH).outcome)

        self.assertEqual(observed, set(OutcomeClass))

    def test_affirmative_diagnostic_distinguishes_self_identity_from_binding(self) -> None:
        result = check_source_ledger(LEDGER_PATH)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.boundary, "provenance:ledger-admission")
        self.assertEqual(result.code, "FRI-IOR-PROVENANCE-100")
        self.assertEqual(result.evidence["binding_mode"], "self-identified-only")
        self.assertEqual(result.evidence["artifact_content_id"], EXPECTED_LEDGER_ARTIFACT_ID)
        self.assertEqual(
            result.evidence["canonical_content_id"],
            EXPECTED_LEDGER_CANONICAL_ID,
        )

        bound = check_source_ledger(
            LEDGER_PATH,
            expected_artifact_id=ArtifactContentId.parse(EXPECTED_LEDGER_ARTIFACT_ID),
        )
        self.assertIs(bound.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(
            bound.evidence["binding_mode"],
            "expected-exact-byte-identity",
        )


if __name__ == "__main__":
    unittest.main()
