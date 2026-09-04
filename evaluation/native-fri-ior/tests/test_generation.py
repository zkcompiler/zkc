"""Tests for private FRI generation and concrete construction checking."""

from __future__ import annotations

from copy import deepcopy
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import fields, replace
import inspect
import io
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import generate as generator  # noqa: E402
from friiormodel.classical_fixtures import (  # noqa: E402
    parse_classical_owner_generation,
)
from friiormodel.commitment import PairOpening  # noqa: E402
from friiormodel.committed import verify_committed_fri  # noqa: E402
from friiormodel.field import Fp, Fp2  # noqa: E402
from friiormodel.fixtures import (  # noqa: E402
    load_fixture,
    parse_private_generation,
    parse_public_inputs,
    parse_public_native_vector,
    parse_relation_initial_oracle,
)
from friiormodel.generation import (  # noqa: E402
    CheckedNativeToCommittedExecution,
    PrivateFriGenerationMaterial,
    PublicFriArtifacts,
    check_native_to_committed_execution,
    generate_honest_native_to_committed_execution,
)
from friiormodel.profile import (  # noqa: E402
    DEFAULT_VALIDATION_LIMITS,
    EXACT_PROFILE,
)
from friiormodel.provenance import ValidationBasisId  # noqa: E402
from friiormodel.proof import PublicFriProof  # noqa: E402
from friiormodel.report import _source_closure  # noqa: E402
from friiormodel.subjects import (  # noqa: E402
    CHECKED_FIAT_SHAMIR_CONSTRUCTION,
    COMMITMENT_COMPILATION_DECLARATION,
    FIAT_SHAMIR_CONSTRUCTION_DECLARATION,
    GRINDING_AUGMENTATION_DECLARATION,
)
from friiormodel.terms import (  # noqa: E402
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
)
from friiormodel.transcript import (  # noqa: E402
    FiatShamirTranscript,
    derive_fiat_shamir_transcript,
)


PACKAGE = Path(__file__).resolve().parents[1]
ROOT = PACKAGE.parents[1]


def _loaded(name: str):
    return load_fixture(ROOT, f"evaluation/native-fri-ior/cases/{name}", name)


def _private_generation_material() -> PrivateFriGenerationMaterial:
    parsed = parse_private_generation(_loaded("owner-generation-input.json").value)
    return PrivateFriGenerationMaterial(
        parsed.coefficients,
        parsed.initial_layer_salts,
        parsed.first_fold_layer_salts,
    )


def _fixture_public_inputs():
    return parse_public_inputs(_loaded("public-inputs.json").value)


def _fp2(real: int, imaginary: int = 0) -> Fp2:
    return Fp2(Fp.reduce(real), Fp.reduce(imaginary))


def _require_primary() -> CheckedNativeToCommittedExecution:
    admission = generate_honest_native_to_committed_execution(
        _private_generation_material(),
        _fixture_public_inputs(),
    )
    if admission.checked_execution is None:
        raise AssertionError(admission.result.to_term())
    return admission.checked_execution


def _replace_proof_opening(
    proof: PublicFriProof,
    table_index: int,
    opening: PairOpening,
) -> PublicFriProof:
    table = list(proof.opening_table)
    table[table_index] = replace(table[table_index], opening=opening)
    return replace(proof, opening_table=tuple(table))


def _all_mapping_keys(value: object) -> tuple[str, ...]:
    if isinstance(value, dict):
        return tuple(value) + tuple(
            key for item in value.values() for key in _all_mapping_keys(item)
        )
    if isinstance(value, list):
        return tuple(key for item in value for key in _all_mapping_keys(item))
    return ()


class PrivateAndPublicLaneTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.checked = _require_primary()

    def test_private_material_has_no_portable_term_or_identity(self) -> None:
        private = _private_generation_material()
        self.assertFalse(hasattr(private, "to_term"))
        self.assertFalse(hasattr(private, "identity"))
        rendered = repr(private)
        self.assertNotIn("3", rendered)
        self.assertNotIn("salt", rendered.lower())

    def test_exact_classical_owner_input_has_an_explicit_nonpublic_role(self) -> None:
        value = deepcopy(_loaded("exact-classical-owner-generation-input.json").value)
        parsed = parse_classical_owner_generation(value)
        self.assertEqual(len(parsed.source_coefficients), 8)
        self.assertGreater(len(parsed.salt_seed), 0)
        value["authority"] = "public-report-input"
        with self.assertRaises(ModelFailure) as caught:
            parse_classical_owner_generation(value)
        self.assertEqual(caught.exception.code, "FRI-IOR-CLASSICAL-FIXTURE-001")

    def test_public_projection_has_only_public_inputs_and_proof(self) -> None:
        projection = self.checked.public_artifacts
        self.assertEqual(
            {item.name for item in fields(PublicFriArtifacts)},
            {"public_inputs", "proof"},
        )
        rendered = repr(projection.to_term()).lower()
        for forbidden in (
            "private_material",
            "source_trace",
            "source_polynomial",
            "complete_logical_oracle",
            "commitment_tree",
        ):
            self.assertNotIn(forbidden, rendered)

    def test_public_projection_verifies_without_owner_local_material(self) -> None:
        projection = self.checked.public_artifacts
        result = verify_committed_fri(
            projection.public_inputs,
            projection.proof,
            ResourceCounter(),
        )
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-COMMITTED-100")

    def test_generation_surface_accepts_limits_not_a_mutable_counter(self) -> None:
        self.assertEqual(
            tuple(
                inspect.signature(
                    generate_honest_native_to_committed_execution
                ).parameters
            ),
            ("private_material", "public_inputs", "limits"),
        )
        admission = generate_honest_native_to_committed_execution(
            _private_generation_material(),
            _fixture_public_inputs(),
            ResourceCounter(),
        )
        self.assertIs(admission.result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-037")

    def test_private_salt_shape_is_checked_at_formation(self) -> None:
        private = _private_generation_material()
        with self.assertRaises(ModelFailure) as raised:
            PrivateFriGenerationMaterial(
                private.coefficients,
                private.initial_layer_salts[:-1],
                private.first_fold_layer_salts,
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-GENERATION-002")

    def test_production_generation_module_has_no_fixture_authority(self) -> None:
        source = (PACKAGE / "friiormodel/generation.py").read_text(encoding="utf-8")
        for forbidden in (
            "PRIMARY_COEFFICIENTS",
            "PRIMARY_STATEMENT",
            "PRIMARY_APPLICATION_CONTEXT",
            "primary_private_generation_material",
            "primary_public_inputs",
            "owner-generation-input.json",
            "public-inputs.json",
        ):
            self.assertNotIn(forbidden, source)

    def test_owner_generator_refuses_a_different_frozen_native_vector(self) -> None:
        expected = parse_public_native_vector(
            _loaded("public-native-vector.json").value
        )
        altered = replace(
            expected,
            query_draws=(
                expected.query_draws[1],
                expected.query_draws[0],
                *expected.query_draws[2:],
            ),
        )
        output = io.StringIO()
        errors = io.StringIO()
        with (
            patch.object(generator, "parse_public_native_vector", return_value=altered),
            redirect_stdout(output),
            redirect_stderr(errors),
        ):
            result = generator.main(["--root", str(ROOT)])
        self.assertEqual(result, 1)
        self.assertEqual(output.getvalue(), "")
        self.assertIn("differs from the frozen public native vector", errors.getvalue())


class OwnerLocalReportIntegrationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = generator.build_owner_local_report(ROOT)

    def test_exact_five_result_chain_is_checked_in_order(self) -> None:
        calls: list[str] = []
        admissions: dict[str, object] = {}
        names = (
            "generate_honest_native_to_committed_execution",
            "generate_native_to_committed_fresh",
            "generate_committed_to_work_fresh",
            "compose_checked_constructions",
            "check_fri_relation_grounding",
        )
        originals = {name: getattr(generator, name) for name in names}

        def recording(name: str):
            def invoke(*args: object, **kwargs: object):
                calls.append(name)
                admission = originals[name](*args, **kwargs)
                admissions[name] = admission
                return admission

            return invoke

        patchers = [
            patch.object(generator, name, side_effect=recording(name)) for name in names
        ]
        for patcher in patchers:
            patcher.start()
        try:
            report = generator.build_owner_local_report(ROOT)
        finally:
            for patcher in reversed(patchers):
                patcher.stop()

        self.assertEqual(calls, list(names))
        self.assertEqual(
            report["checked_results"],
            {
                "concrete_fiat_shamir_execution": "FRI-IOR-GENERATION-100",
                "native_to_committed_fresh": "FRI-IOR-CONSTRUCTION-101",
                "committed_to_work_fresh": "FRI-IOR-CONSTRUCTION-103",
                "construction_composition": "FRI-IOR-CONSTRUCTION-104",
                "relation_grounding": "FRI-IOR-RELATION-102",
            },
        )
        self.assertEqual(
            set(report["checked_capability_ids"]),
            {
                "concrete_fiat_shamir_execution",
                "native_to_committed_fresh",
                "committed_to_work_fresh",
                "construction_composition",
                "relation_grounding",
            },
        )
        self.assertEqual(
            set(report["semantic_result_ids"]),
            {"relation_grounding", "relation_occurrence_map"},
        )
        receipt_attributes = {
            "generate_honest_native_to_committed_execution": "checked_execution",
            "generate_native_to_committed_fresh": "checked_receipt",
            "generate_committed_to_work_fresh": "checked_receipt",
            "compose_checked_constructions": "checked_receipt",
            "check_fri_relation_grounding": "checked_grounding",
        }
        for name, attribute in receipt_attributes.items():
            admission = admissions[name]
            receipt = getattr(admission, attribute)
            self.assertIsNotNone(receipt)
            self.assertEqual(admission.result.subject, receipt.identity)

    def test_owner_summary_is_deterministic(self) -> None:
        outputs: list[str] = []
        for _ in range(2):
            output = io.StringIO()
            errors = io.StringIO()
            with redirect_stdout(output), redirect_stderr(errors):
                result = generator.main(["--root", str(ROOT)])
            self.assertEqual(result, 0)
            self.assertEqual(errors.getvalue(), "")
            outputs.append(output.getvalue())
        self.assertEqual(outputs[0], outputs[1])
        self.assertEqual(json.loads(outputs[0]), self.report)

    def test_fixture_check_rederives_without_changing_the_case_tree(self) -> None:
        cases = PACKAGE / "cases"
        before = {path.name: path.read_bytes() for path in cases.glob("*.json")}
        report = generator.check_frozen_fixtures(ROOT)
        after = {path.name: path.read_bytes() for path in cases.glob("*.json")}
        self.assertEqual(before, after)
        self.assertEqual(report, self.report)

    def test_fixture_check_refuses_a_stale_reviewed_vector(self) -> None:
        candidates = deepcopy(generator.build_frozen_fixture_candidates(ROOT))
        candidates["public-inputs.json"]["application_context"]["suffix"] += 1
        with (
            patch.object(
                generator,
                "build_frozen_fixture_candidates",
                return_value=candidates,
            ),
            self.assertRaisesRegex(RuntimeError, "reviewed fixture is stale"),
        ):
            generator.check_frozen_fixtures(ROOT)

    def test_owner_summary_exports_no_private_generation_material(self) -> None:
        self.assertEqual(
            set(self.report),
            {
                "schema",
                "outcome",
                "public_inputs_id",
                "public_proof_id",
                "native_trace_id",
                "checked_results",
                "checked_capability_ids",
                "semantic_result_ids",
                "relation_input_binding",
                "exact_classical_control",
                "scope",
                "nonclaims",
            },
        )
        keys = tuple(key.lower() for key in _all_mapping_keys(self.report))
        for forbidden_key_part in (
            "coefficient",
            "private",
            "salt",
            "source_trace",
            "logical_oracle",
        ):
            self.assertFalse(
                any(forbidden_key_part in key for key in keys),
                forbidden_key_part,
            )

        rendered = json.dumps(
            self.report,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
        material = _private_generation_material()
        for salt in (
            *material.initial_layer_salts,
            *material.first_fold_layer_salts,
        ):
            self.assertNotIn(salt.hex(), rendered)
        self.assertNotIn(
            json.dumps(
                [coefficient.to_term() for coefficient in material.coefficients],
                separators=(",", ":"),
            ),
            rendered,
        )
        exact_owner = parse_classical_owner_generation(
            _loaded("exact-classical-owner-generation-input.json").value
        )
        self.assertNotIn(exact_owner.salt_seed.hex(), rendered)
        self.assertNotIn(
            json.dumps(
                [coefficient.to_term() for coefficient in exact_owner.source_coefficients],
                separators=(",", ":"),
            ),
            rendered,
        )

    def test_exact_classical_owner_lane_regenerates_frozen_public_terms(self) -> None:
        candidates = generator.build_exact_classical_frozen_fixture_candidates(ROOT)
        self.assertEqual(
            candidates["exact-classical-public-inputs.json"],
            _loaded("exact-classical-public-inputs.json").value,
        )
        self.assertEqual(
            candidates["exact-classical-public-proof.json"],
            _loaded("exact-classical-public-proof.json").value,
        )
        exact = self.report["exact_classical_control"]
        self.assertEqual(
            exact["checked_results"],
            {
                "native": "FRI-IOR-CLASSICAL-NATIVE-100",
                "fresh": "FRI-IOR-CLASSICAL-COMMITTED-100",
                "fiat_shamir": "FRI-IOR-CLASSICAL-COMMITTED-100",
            },
        )

    def test_receipt_result_splicing_is_not_accepted_by_owner_boundary(self) -> None:
        admission = generator.generate_honest_native_to_committed_execution(
            _private_generation_material(),
            _fixture_public_inputs(),
        )
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIsNotNone(admission.checked_execution)
        spliced = replace(
            admission,
            result=replace(admission.result, subject=EXACT_PROFILE.identity),
        )
        with self.assertRaisesRegex(RuntimeError, "receipt"):
            generator._require_receipt(
                spliced,
                "checked_execution",
                "spliced generation",
                generator.CheckedNativeToCommittedExecution,
                "FRI-IOR-GENERATION-100",
                "generation:concrete-construction-check",
            )

    def test_live_receipts_anchor_the_relation_result_and_public_artifacts(
        self,
    ) -> None:
        observed: dict[str, object] = {}
        original = generator.canonical_relation_grounding_request

        def capture(
            statement: object,
            relation_oracle: object,
            commitment_receipt: object,
            composition_receipt: object,
            public_inputs: object,
            proof: object,
        ):
            observed.update(
                relation_oracle=relation_oracle,
                commitment_receipt=commitment_receipt,
                composition_receipt=composition_receipt,
                public_inputs=public_inputs,
                proof=proof,
            )
            return original(
                statement,
                relation_oracle,
                commitment_receipt,
                composition_receipt,
                public_inputs,
                proof,
            )

        with patch.object(
            generator,
            "canonical_relation_grounding_request",
            side_effect=capture,
        ):
            report = generator.build_owner_local_report(ROOT)

        commitment = observed["commitment_receipt"]
        composition = observed["composition_receipt"]
        public_inputs = observed["public_inputs"]
        proof = observed["proof"]
        relation_oracle = observed["relation_oracle"]
        self.assertEqual(
            report["checked_capability_ids"]["native_to_committed_fresh"],
            commitment.identity.to_term(),
        )
        self.assertEqual(
            report["checked_capability_ids"]["construction_composition"],
            composition.identity.to_term(),
        )
        self.assertEqual(composition.commitment_receipt_id, commitment.identity)
        self.assertEqual(
            composition.fiat_shamir_public_inputs_id,
            public_inputs.identity,
        )
        self.assertEqual(composition.fiat_shamir_public_proof_id, proof.identity)
        self.assertEqual(
            relation_oracle,
            commitment.candidate.source_trace.initial_oracle,
        )
        self.assertIsNot(
            relation_oracle,
            commitment.candidate.source_trace.initial_oracle,
        )

    def test_a_live_receipt_from_another_run_cannot_be_mixed_into_grounding(
        self,
    ) -> None:
        checked = _require_primary()
        trace = checked.candidate.source_trace
        public_inputs = checked.public_artifacts.public_inputs
        alternate = generator.generate_native_to_committed_fresh(
            _private_generation_material(),
            {"case": "independently-issued-alternate-receipt"},
            public_inputs.application_context,
            trace.beta0,
            trace.beta1,
            tuple(draw.initial_domain_index for draw in trace.query_draws),
        )
        self.assertIs(alternate.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertIsNotNone(alternate.checked_receipt)
        alternate_receipt = alternate.checked_receipt
        assert alternate_receipt is not None

        original = generator.check_fri_relation_grounding

        def substitute_live_receipt(
            request: object,
            relation_oracle: object,
            commitment_receipt: object,
            composition_receipt: object,
            supplied_inputs: object,
            proof: object,
            limits: object,
        ):
            self.assertNotEqual(alternate_receipt.identity, commitment_receipt.identity)
            return original(
                request,
                relation_oracle,
                alternate_receipt,
                composition_receipt,
                supplied_inputs,
                proof,
                limits,
            )

        with (
            patch.object(
                generator,
                "check_fri_relation_grounding",
                side_effect=substitute_live_receipt,
            ),
            self.assertRaisesRegex(
                RuntimeError,
                "relation grounding refused: FRI-IOR-RELATION-024",
            ),
        ):
            generator.build_owner_local_report(ROOT)

    def test_relation_oracle_is_loaded_from_its_own_fixture_and_checked(
        self,
    ) -> None:
        relation_fixture = _loaded("owner-relation-input.json")
        relation_oracle = parse_relation_initial_oracle(relation_fixture.value)
        expected_trace = parse_public_native_vector(
            _loaded("public-native-vector.json").value
        )
        self.assertEqual(relation_oracle, expected_trace.initial_oracle)
        self.assertIsNot(relation_oracle, expected_trace.initial_oracle)

        entries = list(relation_oracle.entries)
        entries[0] = replace(entries[0], value=entries[0].value + _fp2(1))
        independently_changed = replace(relation_oracle, entries=tuple(entries))
        with (
            patch.object(
                generator,
                "parse_relation_initial_oracle",
                return_value=independently_changed,
            ),
            self.assertRaisesRegex(
                RuntimeError,
                "relation grounding refused: FRI-IOR-RELATION-078",
            ),
        ):
            generator.build_owner_local_report(ROOT)

    def test_refreeze_checks_incompatible_relation_before_any_fixture_write(
        self,
    ) -> None:
        relation_fixture = _loaded("owner-relation-input.json")
        altered_value = deepcopy(relation_fixture.value)
        first_value = altered_value["oracle"]["entries"][0]["value"]
        first_value[0] = (first_value[0] + 1) % 97
        altered_raw = generator.canonical_pretty_json(altered_value)
        altered_fixture = replace(
            relation_fixture,
            artifact_id=generator.artifact_content_id(altered_raw),
            canonical_id=generator.canonical_json_content_id(altered_value),
            value=altered_value,
            raw=altered_raw,
        )
        original_load = generator.load_fixture

        def substitute_relation(root: Path, relative: str, role: str):
            if relative.endswith("/owner-relation-input.json"):
                return altered_fixture
            return original_load(root, relative, role)

        names = (
            *generator._DERIVED_PUBLIC_CASES.values(),
            "expected-results.json",
        )
        before = {
            name: (PACKAGE / "cases" / name).read_bytes()
            for name in names
        }
        with (
            patch.object(generator, "load_fixture", side_effect=substitute_relation),
            patch.object(generator, "_write_fixture") as writer,
            self.assertRaisesRegex(
                RuntimeError,
                "relation grounding refused: FRI-IOR-RELATION-078",
            ),
        ):
            generator.refreeze_frozen_fixtures(ROOT)
        writer.assert_not_called()
        self.assertEqual(
            before,
            {
                name: (PACKAGE / "cases" / name).read_bytes()
                for name in names
            },
        )


class HonestGenerationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.checked = _require_primary()
        cls.candidate = cls.checked.candidate
        cls.projection = cls.checked.public_artifacts
        transcript = derive_fiat_shamir_transcript(
            cls.projection.public_inputs.transcript_plan,
            cls.projection.public_inputs.statement,
            cls.projection.public_inputs.application_context,
            cls.projection.proof.cap0,
            cls.projection.proof.cap1,
            cls.projection.proof.terminal_coefficients,
            cls.projection.proof.grinding_nonce,
            ResourceCounter(),
        )
        if not isinstance(transcript, FiatShamirTranscript):
            raise AssertionError(transcript.to_term())
        cls.transcript = transcript

    def test_private_fixture_generates_the_exact_public_native_vector(self) -> None:
        private = self.candidate.private_material
        expected_private = _private_generation_material()
        expected_trace = parse_public_native_vector(
            _loaded("public-native-vector.json").value
        )
        self.assertEqual(
            private.coefficients,
            expected_private.coefficients,
        )
        self.assertEqual(
            private.initial_layer_salts, expected_private.initial_layer_salts
        )
        self.assertEqual(
            private.first_fold_layer_salts,
            expected_private.first_fold_layer_salts,
        )
        self.assertEqual(self.candidate.source_trace, expected_trace)
        self.assertEqual(self.transcript.beta0, expected_trace.beta0)
        self.assertEqual(self.transcript.beta1, expected_trace.beta1)
        self.assertEqual(
            tuple(
                occurrence.initial_domain_index
                for occurrence in self.transcript.query_occurrences
            ),
            tuple(draw.initial_domain_index for draw in expected_trace.query_draws),
        )

    def test_checked_receipt_binds_every_construction_subject(self) -> None:
        candidate = self.candidate
        self.assertEqual(
            candidate.commitment_compilation_declaration_id,
            COMMITMENT_COMPILATION_DECLARATION.identity,
        )
        self.assertEqual(
            candidate.grinding_augmentation_declaration_id,
            GRINDING_AUGMENTATION_DECLARATION.identity,
        )
        self.assertEqual(
            candidate.fiat_shamir_construction_declaration_id,
            FIAT_SHAMIR_CONSTRUCTION_DECLARATION.identity,
        )
        self.assertEqual(
            candidate.checked_fiat_shamir_construction_id,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION.identity,
        )

    def test_occurrence_map_preserves_antipodal_opening_reuse(self) -> None:
        occurrence_map = self.candidate.occurrence_map
        self.assertEqual(tuple(entry.ordinal for entry in occurrence_map), (0, 1, 2, 3))
        self.assertEqual(
            tuple(entry.initial_domain_index for entry in occurrence_map),
            (3, 15, 11, 10),
        )
        self.assertNotEqual(
            occurrence_map[0].source_initial_query_id,
            occurrence_map[2].source_initial_query_id,
        )
        self.assertEqual(
            occurrence_map[0].target_initial_opening_id,
            occurrence_map[2].target_initial_opening_id,
        )
        self.assertEqual(
            occurrence_map[0].target_first_fold_opening_id,
            occurrence_map[2].target_first_fold_opening_id,
        )
        self.assertEqual(
            occurrence_map[0].initial_layer_table_index,
            occurrence_map[2].initial_layer_table_index,
        )
        self.assertEqual(
            occurrence_map[0].first_fold_layer_table_index,
            occurrence_map[2].first_fold_layer_table_index,
        )

    def test_receipt_records_decision_and_commutation_without_security_claims(
        self,
    ) -> None:
        admission = check_native_to_committed_execution(self.candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-100")
        evidence = admission.result.evidence
        self.assertTrue(evidence["decisions_equal"])
        self.assertTrue(evidence["complete_commitment_caps_equal"])
        self.assertTrue(evidence["sampled_answer_pairs_equal"])
        self.assertTrue(evidence["challenge_and_query_trace_equal"])
        self.assertFalse(evidence["establishes_general_compiler_correctness"])
        self.assertFalse(evidence["establishes_commitment_security"])
        self.assertFalse(evidence["establishes_proximity_theorem"])
        self.assertFalse(evidence["establishes_protocol_security"])

    def test_validation_basis_changes_without_changing_execution_semantics(
        self,
    ) -> None:
        alternate_limits = replace(
            DEFAULT_VALIDATION_LIMITS,
            field_operations=1000,
        )
        admission = check_native_to_committed_execution(
            self.candidate,
            alternate_limits,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        alternate = admission.checked_execution
        assert alternate is not None
        self.assertEqual(
            alternate.semantic_execution_id,
            self.checked.semantic_execution_id,
        )
        self.assertNotEqual(
            alternate.validation_basis_id,
            self.checked.validation_basis_id,
        )
        self.assertNotEqual(alternate.identity, self.checked.identity)

    def test_validation_basis_binds_the_exact_checker_source_closure(self) -> None:
        self.assertIsInstance(self.checked.validation_basis_id, ValidationBasisId)
        manifest = self.checked.validation_source_manifest
        self.assertEqual(
            tuple(source.path for source in manifest),
            _source_closure(ROOT, ("generation.py",)),
        )
        self.assertTrue(
            all(
                source.artifact_content_id.startswith("sha256:")
                and source.byte_length > 0
                for source in manifest
            )
        )
        term = self.checked.to_term()["validation"]
        self.assertEqual(term["basis_id"], str(self.checked.validation_basis_id))
        self.assertEqual(len(term["source_manifest"]), len(manifest))

    def test_resource_snapshot_is_complete_and_frozen(self) -> None:
        snapshot = self.checked.resource_snapshot
        self.assertEqual(
            set(snapshot.to_term()), set(DEFAULT_VALIDATION_LIMITS.to_term())
        )
        self.assertGreater(snapshot.field_operations, 0)
        self.assertEqual(snapshot.logical_query_occurrences, 24)
        self.assertEqual(snapshot.unique_openings, 5)
        with self.assertRaises(AttributeError):
            snapshot.field_operations = 0


class CorrespondenceRefusalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.checked = _require_primary()
        cls.candidate = cls.checked.candidate

    def test_mismatched_source_trace_is_not_revalidated(self) -> None:
        trace = self.candidate.source_trace
        entries = list(trace.initial_oracle.entries)
        entries[0] = replace(
            entries[0],
            value=entries[0].value + _fp2(1),
        )
        altered_oracle = replace(trace.initial_oracle, entries=tuple(entries))
        altered_trace = replace(trace, initial_oracle=altered_oracle)
        candidate = replace(
            self.candidate,
            source_trace=altered_trace,
            claimed_source_trace_id=altered_trace.identity,
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-026")

    def test_mismatched_private_commitment_advice_is_refused(self) -> None:
        private = self.candidate.private_material
        salts = list(private.initial_layer_salts)
        salts[0] = bytes((salts[0][0] ^ 1,)) + salts[0][1:]
        candidate = replace(
            self.candidate,
            private_material=PrivateFriGenerationMaterial(
                private.coefficients,
                tuple(salts),
                private.first_fold_layer_salts,
            ),
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-027")

    def test_mismatched_target_proof_is_checked_not_silently_rebound(self) -> None:
        proof = self.candidate.public_artifacts.proof
        opening = proof.opening_table[0].opening
        bad_salt = bytes((opening.salt[0] ^ 1,)) + opening.salt[1:]
        altered_proof = _replace_proof_opening(
            proof,
            0,
            replace(opening, salt=bad_salt),
        )
        artifacts = replace(self.candidate.public_artifacts, proof=altered_proof)
        candidate = replace(
            self.candidate,
            public_artifacts=artifacts,
            claimed_proof_id=altered_proof.identity,
            claimed_target_decision="Reject",
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-COMMITMENT-025")

    def test_profile_mismatch_precedes_transcript_or_proof_work(self) -> None:
        unsupported_profile = replace(EXACT_PROFILE, name="alternate-fri-profile")
        inputs = replace(
            self.candidate.public_artifacts.public_inputs,
            profile=unsupported_profile,
        )
        artifacts = replace(self.candidate.public_artifacts, public_inputs=inputs)
        candidate = replace(self.candidate, public_artifacts=artifacts)
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-019")

    def test_occurrence_map_mismatch_is_refused(self) -> None:
        occurrence_map = list(self.candidate.occurrence_map)
        occurrence_map[0] = replace(
            occurrence_map[0],
            initial_domain_index=(occurrence_map[0].initial_domain_index + 1) % 16,
        )
        candidate = replace(self.candidate, occurrence_map=tuple(occurrence_map))
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-034")

    def test_stale_source_target_and_trace_bindings_are_distinct(self) -> None:
        stale_candidates = (
            (
                replace(
                    self.candidate,
                    claimed_source_trace_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-021",
            ),
            (
                replace(
                    self.candidate,
                    claimed_public_inputs_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-022",
            ),
            (
                replace(
                    self.candidate,
                    claimed_proof_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-023",
            ),
            (
                replace(
                    self.candidate,
                    claimed_target_trace_id=EXACT_PROFILE.identity,
                ),
                "FRI-IOR-GENERATION-025",
            ),
        )
        for candidate, code in stale_candidates:
            with self.subTest(code=code):
                admission = check_native_to_committed_execution(candidate)
                self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(admission.result.code, code)

    def test_wrong_construction_subject_is_a_kind_mismatch(self) -> None:
        candidate = replace(
            self.candidate,
            commitment_compilation_declaration_id=EXACT_PROFILE.identity,
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.KIND_MISMATCH)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-024")

    def test_stale_decision_claim_is_refused(self) -> None:
        candidate = replace(
            self.candidate,
            claimed_source_decision="Reject",
        )
        admission = check_native_to_committed_execution(candidate)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-GENERATION-029")

    def test_generation_resource_exhaustion_is_typed_and_atomic(self) -> None:
        limits = replace(DEFAULT_VALIDATION_LIMITS, field_operations=0)
        admission = generate_honest_native_to_committed_execution(
            _private_generation_material(),
            _fixture_public_inputs(),
            limits,
        )
        self.assertIs(
            admission.result.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(admission.result.code, "FRI-IOR-RESOURCE-008")
        self.assertIsNone(admission.checked_execution)

    def test_wrong_candidate_and_mutable_counter_are_malformed(self) -> None:
        wrong_candidate = check_native_to_committed_execution(object())
        self.assertIs(wrong_candidate.result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(wrong_candidate.result.code, "FRI-IOR-GENERATION-017")
        wrong_limits = check_native_to_committed_execution(
            self.candidate,
            ResourceCounter(),
        )
        self.assertIs(wrong_limits.result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(wrong_limits.result.code, "FRI-IOR-GENERATION-018")


if __name__ == "__main__":
    unittest.main()
