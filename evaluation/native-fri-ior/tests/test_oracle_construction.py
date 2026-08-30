"""Tests for the exact reusable oracle-commitment construction authority."""

from __future__ import annotations

import copy
from dataclasses import replace
from pathlib import Path
import pickle
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.classical import (  # noqa: E402
    ClassicalCommittedCase,
    DEFAULT_CLASSICAL_LIMITS,
    EXACT_CLASSICAL_COMMITTED_CORE,
    EXACT_CLASSICAL_COMMITMENT_PROFILE,
    EXACT_CLASSICAL_FRI_PROFILE,
    EXACT_CLASSICAL_NATIVE_CORE,
    GoldilocksElement,
    build_honest_classical_case,
)
from friiormodel.oracle_construction import (  # noqa: E402
    CheckedOracleCommitmentConstruction,
    CONSTRUCTION_NONCLAIMS,
    EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION,
    EXACT_ORACLE_COMMITMENT_PROFILE,
    OracleCommitmentAdvice,
    OracleCommitmentCapability,
    OracleCommitmentConstructionDefect,
    OracleCommitmentRunReceipt,
    admit_oracle_commitment_construction,
    check_oracle_commitment_run,
    derive_oracle_commitment_static_maps,
    elaborate_committed_core,
    form_oracle_commitment_advice,
)
from friiormodel.terms import (  # noqa: E402
    ModelFailure,
    OutcomeClass,
    semantic_id,
)


def _other_id(label: str = "other"):
    return semantic_id(
        "classical-fri-test-subject",
        "classical-fri.test-subject.v1",
        label,
    )


def _require_admission():
    admission = admit_oracle_commitment_construction(
        EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION
    )
    if admission.checked_construction is None or admission.capability is None:
        raise AssertionError(admission.result.to_term())
    return admission


def _require_run(case=None):
    admission = _require_admission()
    assert admission.capability is not None
    if case is None:
        case = build_honest_classical_case()
    advice = form_oracle_commitment_advice(
        admission.capability,
        case,
        case.owner_salts,
    )
    run_admission = check_oracle_commitment_run(
        admission.capability,
        case,
        advice,
    )
    if run_admission.receipt is None:
        raise AssertionError(run_admission.result.to_term())
    return admission, case, advice, run_admission


class ExactStructuralConstructionTest(unittest.TestCase):
    def test_bounded_elaboration_reconstructs_the_independent_target(self) -> None:
        maps = derive_oracle_commitment_static_maps()
        elaborated = elaborate_committed_core(
            EXACT_CLASSICAL_NATIVE_CORE,
            EXACT_ORACLE_COMMITMENT_PROFILE,
            maps,
        )
        self.assertEqual(elaborated.to_term(), EXACT_CLASSICAL_COMMITTED_CORE.to_term())
        self.assertEqual(elaborated.identity, EXACT_CLASSICAL_COMMITTED_CORE.identity)
        self.assertEqual(
            EXACT_ORACLE_COMMITMENT_PROFILE.source_profile_id,
            EXACT_CLASSICAL_FRI_PROFILE.identity,
        )
        self.assertEqual(
            EXACT_ORACLE_COMMITMENT_PROFILE.commitment_semantics_id,
            EXACT_CLASSICAL_COMMITMENT_PROFILE.identity,
        )

    def test_admission_derives_total_static_maps_and_intrinsic_bounds(self) -> None:
        admission = _require_admission()
        checked = admission.checked_construction
        assert checked is not None
        maps = checked.maps
        self.assertIs(admission.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(admission.result.code, "FRI-IOR-CLASSICAL-CONSTRUCTION-100")
        self.assertEqual(checked.construction_id, admission.result.subject)
        self.assertEqual(
            admission.result.evidence["scope"],
            "profile-wide-structural-construction-only",
        )
        self.assertIs(
            admission.result.evidence["concrete_run_validation_required"],
            True,
        )
        self.assertEqual(len(maps.public_environment_map), 2)
        self.assertEqual(
            tuple(entry.semantic_purpose for entry in maps.public_environment_map),
            ("Statement", "ApplicationContext"),
        )
        self.assertEqual(len(maps.publication_map), 3)
        self.assertEqual(len(maps.fresh_coin_map), 3)
        self.assertEqual(len(maps.query_draw_map), 4)
        self.assertEqual(len(maps.answer_opening_map), 12)
        self.assertEqual(
            tuple(entry.occurrence_ordinal for entry in maps.answer_opening_map),
            tuple(range(12)),
        )
        self.assertEqual(
            len(
                {
                    entry.target_logical_opening_coordinate
                    for entry in maps.answer_opening_map
                }
            ),
            12,
        )
        self.assertEqual(
            {entry.target_authentication_check for entry in maps.answer_opening_map},
            {"authenticate-canonical-opening-table"},
        )
        self.assertEqual(
            tuple(
                entry.target_check
                for entry in maps.check_map
                if entry.source_check is None
            ),
            (
                "authenticate-canonical-opening-table",
                "opening-table-coverage-and-selector-check",
            ),
        )
        self.assertEqual(
            tuple(entry.protected_publication_prefix for entry in maps.fresh_coin_map),
            (("M0",), ("M0", "M1"), ("M0", "M1", "M2")),
        )
        self.assertEqual(
            tuple(
                (entry.source_outcome, entry.target_outcome)
                for entry in maps.outcome_map
            ),
            (("Accept", "Accept"), ("Reject", "Reject")),
        )
        bounds = checked.intrinsic_bounds
        self.assertEqual(bounds.publication_roots, 3)
        self.assertEqual(bounds.fresh_coins, 3)
        self.assertEqual(bounds.query_draws, 4)
        self.assertEqual(bounds.logical_layer_query_occurrences, 12)
        self.assertEqual(bounds.max_unique_physical_openings, 12)
        self.assertEqual(bounds.owner_salt_leaves, 56)
        self.assertEqual(bounds.owner_salt_bytes, 896)
        self.assertEqual(bounds.commitment_leaf_hashes, 56)
        self.assertEqual(bounds.commitment_internal_hashes, 53)
        self.assertEqual(bounds.max_public_authentication_node_hashes, 48)
        self.assertEqual(bounds.max_public_opening_payload_bytes, 1920)

    def test_construction_subject_has_no_authored_commutation_or_security_claim(
        self,
    ) -> None:
        term = EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION.to_term()
        rendered = repr(term).lower()
        self.assertNotIn("commutes", rendered)
        self.assertNotIn("corresponds", rendered)
        self.assertNotIn("maps", term)
        self.assertNotIn("public_replay_closure", term)
        self.assertNotIn("intrinsic_bounds", term)
        self.assertIn("static_elaboration_law", term)
        self.assertIn("advice_schema_id", term)
        self.assertNotIn("nonclaims", term)
        self.assertIn(
            "commitment-binding-hiding-or-extractability",
            CONSTRUCTION_NONCLAIMS,
        )
        self.assertIn("universal-fri-family-compilation", CONSTRUCTION_NONCLAIMS)
        self.assertIn(
            "universal-execution-commutation-without-per-run-validation",
            CONSTRUCTION_NONCLAIMS,
        )
        closure = derive_oracle_commitment_static_maps()
        self.assertEqual(len(closure.answer_opening_map), 12)

    def test_admission_refuses_a_stale_map_after_rederivation(self) -> None:
        declaration = EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION
        bad_maps = replace(
            declaration.maps,
            publication_map=declaration.maps.publication_map[:-1],
        )
        admission = admit_oracle_commitment_construction(
            replace(declaration, maps=bad_maps)
        )
        self.assertEqual(
            replace(declaration, maps=bad_maps).identity,
            declaration.identity,
        )
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-CLASSICAL-CONSTRUCTION-016")
        self.assertEqual(
            admission.result.evidence["defect"],
            OracleCommitmentConstructionDefect.MAP_COVERAGE_MISMATCH.value,
        )
        self.assertIsNone(admission.checked_construction)
        self.assertIsNone(admission.capability)

    def test_admission_refuses_a_stale_target_identity(self) -> None:
        declaration = replace(
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION,
            target_core_id=_other_id("stale-target"),
        )
        admission = admit_oracle_commitment_construction(declaration)
        self.assertIs(admission.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(admission.result.code, "FRI-IOR-CLASSICAL-CONSTRUCTION-014")
        self.assertEqual(
            admission.result.evidence["defect"],
            OracleCommitmentConstructionDefect.TARGET_CORE_MISMATCH.value,
        )


class ProcessLocalAuthorityTest(unittest.TestCase):
    def test_direct_checked_result_and_capability_construction_are_blocked(
        self,
    ) -> None:
        declaration = EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION
        with self.assertRaises(ModelFailure) as checked_error:
            CheckedOracleCommitmentConstruction(declaration, _token=object())
        self.assertIs(
            checked_error.exception.outcome,
            OutcomeClass.MISSING_DEPENDENCY,
        )
        admitted = _require_admission()
        assert admitted.checked_construction is not None
        with self.assertRaises(ModelFailure) as capability_error:
            OracleCommitmentCapability(
                admitted.checked_construction,
                _token=object(),
            )
        self.assertIs(
            capability_error.exception.outcome,
            OutcomeClass.MISSING_DEPENDENCY,
        )

    def test_each_admission_mints_fresh_nonserializable_authority(self) -> None:
        first = _require_admission()
        second = _require_admission()
        assert first.checked_construction is not None
        assert second.checked_construction is not None
        assert first.capability is not None
        assert second.capability is not None
        self.assertEqual(
            first.checked_construction.construction_id,
            second.checked_construction.construction_id,
        )
        self.assertIsNot(
            first.checked_construction.result_ref,
            second.checked_construction.result_ref,
        )
        self.assertIsNot(first.capability, second.capability)
        self.assertFalse(hasattr(first.checked_construction, "identity"))
        self.assertFalse(hasattr(first.checked_construction, "to_term"))
        for value in (
            first.checked_construction,
            first.checked_construction.result_ref,
            first.capability,
        ):
            with self.assertRaises(TypeError):
                pickle.dumps(value)
            with self.assertRaises(TypeError):
                copy.copy(value)
            with self.assertRaises(TypeError):
                copy.deepcopy(value)


class ExactConcreteRunConstructionTest(unittest.TestCase):
    def test_one_run_is_independently_checked_and_receipt_is_portable(self) -> None:
        construction, case, advice, run = _require_run()
        assert construction.capability is not None
        assert run.receipt is not None
        receipt = run.receipt
        self.assertIs(run.result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(run.result.code, "FRI-IOR-CLASSICAL-CONSTRUCTION-101")
        self.assertEqual(run.result.subject, receipt.semantic_receipt_id)
        self.assertEqual(
            run.result.evidence["validation_basis_id"],
            receipt.validation_basis_id,
        )
        self.assertEqual(
            receipt.construction_id,
            EXACT_ORACLE_COMMITMENT_CONSTRUCTION_DECLARATION.identity,
        )
        self.assertEqual(receipt.source_core_id, EXACT_CLASSICAL_NATIVE_CORE.identity)
        self.assertEqual(
            receipt.target_core_id,
            EXACT_CLASSICAL_COMMITTED_CORE.identity,
        )
        self.assertEqual(receipt.source_execution_id, case.native_trace.identity)
        self.assertEqual(receipt.target_execution_id, case.fresh_run.identity)
        self.assertEqual(
            receipt.public_environment_id,
            case.native_trace.public_environment.identity,
        )
        self.assertEqual(len(receipt.publication_root_ids), 3)
        self.assertEqual(len(receipt.occurrence_opening_map), 12)
        self.assertEqual(
            tuple(
                binding.occurrence_ordinal
                for binding in receipt.occurrence_opening_map
            ),
            tuple(range(12)),
        )
        self.assertEqual(
            {
                binding.opening_table_index
                for binding in receipt.occurrence_opening_map
            },
            set(range(len(receipt.public_opening_ids))),
        )
        self.assertEqual(len(receipt.public_opening_ids), 11)
        self.assertEqual(
            receipt.occurrence_opening_map[2].opening_table_index,
            receipt.occurrence_opening_map[5].opening_table_index,
        )
        self.assertNotEqual(
            receipt.occurrence_opening_map[2].occurrence_id,
            receipt.occurrence_opening_map[5].occurrence_id,
        )
        self.assertEqual(receipt.construction_resource_usage.hash_calls, 109)
        self.assertGreater(receipt.target_resource_usage.hash_calls, 0)
        self.assertEqual(receipt.source_resource_usage.hash_calls, 0)
        self.assertEqual(pickle.loads(pickle.dumps(receipt)), receipt)
        self.assertFalse(hasattr(receipt, "receipt_id"))
        self.assertFalse(hasattr(receipt, "identity"))
        self.assertEqual(
            receipt.to_term()["semantic_receipt_id"],
            receipt.semantic_receipt_id.to_term(),
        )
        self.assertEqual(
            receipt.to_term()["validation_basis_id"],
            receipt.validation_basis_id.to_term(),
        )
        rendered = repr(receipt.to_term()).lower()
        self.assertNotIn("owner_salts", rendered)
        self.assertNotIn("complete-g0", rendered)
        for owner_local in (advice, construction.capability):
            with self.assertRaises(TypeError):
                pickle.dumps(owner_local)

    def test_two_valid_runs_share_construction_but_not_receipt_identity(self) -> None:
        first_case = build_honest_classical_case()
        second_coefficients = tuple(
            GoldilocksElement(value)
            for value in (2, 3, 5, 7, 11, 13, 17, 19)
        )
        second_case = build_honest_classical_case(
            statement={"claim": "a distinct exact bounded invocation"},
            source_coefficients=second_coefficients,
        )
        _, _, _, first = _require_run(first_case)
        _, _, _, second = _require_run(second_case)
        assert first.receipt is not None
        assert second.receipt is not None
        self.assertEqual(
            first.receipt.construction_id,
            second.receipt.construction_id,
        )
        self.assertNotEqual(first.receipt.invocation_id, second.receipt.invocation_id)
        self.assertNotEqual(
            first.receipt.source_execution_id,
            second.receipt.source_execution_id,
        )
        self.assertNotEqual(
            first.receipt.target_execution_id,
            second.receipt.target_execution_id,
        )
        self.assertNotEqual(
            first.receipt.semantic_receipt_id,
            second.receipt.semantic_receipt_id,
        )

    def test_resource_basis_rotates_without_rotating_semantic_receipt(self) -> None:
        construction = _require_admission()
        assert construction.capability is not None
        case = build_honest_classical_case()
        advice = form_oracle_commitment_advice(
            construction.capability,
            case,
            case.owner_salts,
        )
        first = check_oracle_commitment_run(
            construction.capability,
            case,
            advice,
            DEFAULT_CLASSICAL_LIMITS,
        )
        alternate_limits = replace(
            DEFAULT_CLASSICAL_LIMITS,
            field_operations=DEFAULT_CLASSICAL_LIMITS.field_operations + 1,
        )
        second = check_oracle_commitment_run(
            construction.capability,
            case,
            advice,
            alternate_limits,
        )
        assert first.receipt is not None
        assert second.receipt is not None

        self.assertEqual(
            first.receipt.semantic_receipt_term(),
            second.receipt.semantic_receipt_term(),
        )
        self.assertEqual(
            first.receipt.semantic_receipt_id,
            second.receipt.semantic_receipt_id,
        )
        self.assertNotEqual(
            first.receipt.validation_basis_term(),
            second.receipt.validation_basis_term(),
        )
        self.assertNotEqual(
            first.receipt.validation_basis_id,
            second.receipt.validation_basis_id,
        )
        self.assertEqual(first.result.subject, second.result.subject)
        self.assertEqual(
            first.result.evidence["validation_basis_id"],
            first.receipt.validation_basis_id,
        )
        self.assertEqual(
            second.result.evidence["validation_basis_id"],
            second.receipt.validation_basis_id,
        )

    def test_receipt_ids_and_checked_data_cannot_substitute_for_capability(
        self,
    ) -> None:
        construction, case, advice, run = _require_run()
        assert construction.checked_construction is not None
        assert run.receipt is not None
        for inert in (
            run.receipt,
            run.receipt.semantic_receipt_id,
            run.receipt.validation_basis_id,
            run.receipt.construction_id,
            construction.checked_construction,
            construction.checked_construction.result_ref,
        ):
            result = check_oracle_commitment_run(inert, case, advice)
            self.assertIs(result.result.outcome, OutcomeClass.MISSING_DEPENDENCY)
            self.assertEqual(result.result.code, "FRI-IOR-CLASSICAL-CONSTRUCTION-044")
            self.assertIsNone(result.receipt)

    def test_advice_is_pair_bound_and_root_reconstruction_is_authoritative(
        self,
    ) -> None:
        construction = _require_admission()
        assert construction.capability is not None
        first_case = build_honest_classical_case()
        changed_case = build_honest_classical_case(
            source_coefficients=tuple(
                GoldilocksElement(value)
                for value in (2, 3, 5, 7, 11, 13, 17, 19)
            )
        )
        first_advice = form_oracle_commitment_advice(
            construction.capability,
            first_case,
            first_case.owner_salts,
        )
        stale = check_oracle_commitment_run(
            construction.capability,
            changed_case,
            first_advice,
        )
        self.assertIs(stale.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(stale.result.code, "FRI-IOR-CLASSICAL-CONSTRUCTION-060")

        changed_salts = [list(layer) for layer in first_case.owner_salts]
        changed_salts[0][0] = bytes((changed_salts[0][0][0] ^ 1,)) + bytes(
            changed_salts[0][0][1:]
        )
        tampered_case = replace(
            first_case,
            owner_salts=tuple(tuple(layer) for layer in changed_salts),
        )
        tampered_advice = form_oracle_commitment_advice(
            construction.capability,
            tampered_case,
            tampered_case.owner_salts,
        )
        root_mismatch = check_oracle_commitment_run(
            construction.capability,
            tampered_case,
            tampered_advice,
        )
        self.assertIs(root_mismatch.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(
            root_mismatch.result.code,
            "FRI-IOR-CLASSICAL-CONSTRUCTION-052",
        )

    def test_run_checker_refuses_public_environment_substitution(self) -> None:
        construction = _require_admission()
        assert construction.capability is not None
        case = build_honest_classical_case()
        changed = build_honest_classical_case(
            statement={"claim": "unrelated-public-statement"},
        )

        # Bypass the convenience case constructor to exercise the checker as
        # the authority boundary against a hostile carrier.
        mismatched = object.__new__(ClassicalCommittedCase)
        object.__setattr__(mismatched, "native_trace", case.native_trace)
        object.__setattr__(mismatched, "fresh_run", changed.fresh_run)
        object.__setattr__(mismatched, "fiat_shamir_run", changed.fiat_shamir_run)
        object.__setattr__(mismatched, "owner_salts", changed.owner_salts)
        advice = form_oracle_commitment_advice(
            construction.capability,
            mismatched,
            mismatched.owner_salts,
        )
        result = check_oracle_commitment_run(
            construction.capability,
            mismatched,
            advice,
        )
        self.assertIs(result.result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.result.code, "FRI-IOR-CLASSICAL-CONSTRUCTION-064")
        self.assertIsNone(result.receipt)

    def test_owner_local_and_receipt_constructors_are_not_public_authority(
        self,
    ) -> None:
        construction, case, _, run = _require_run()
        assert run.receipt is not None
        with self.assertRaises(ModelFailure) as advice_error:
            OracleCommitmentAdvice(
                construction_id=run.receipt.construction_id,
                invocation_id=run.receipt.invocation_id,
                salts_by_layer=case.owner_salts,
                _token=object(),
            )
        self.assertIs(advice_error.exception.outcome, OutcomeClass.MISSING_DEPENDENCY)

        receipt = run.receipt
        with self.assertRaises(ModelFailure) as receipt_error:
            OracleCommitmentRunReceipt(
                construction_id=receipt.construction_id,
                source_core_id=receipt.source_core_id,
                target_core_id=receipt.target_core_id,
                invocation_id=receipt.invocation_id,
                source_execution_id=receipt.source_execution_id,
                target_execution_id=receipt.target_execution_id,
                public_environment_id=receipt.public_environment_id,
                publication_root_ids=receipt.publication_root_ids,
                public_opening_ids=receipt.public_opening_ids,
                occurrence_opening_map=receipt.occurrence_opening_map,
                validation_limits=DEFAULT_CLASSICAL_LIMITS,
                source_resource_usage=receipt.source_resource_usage,
                target_resource_usage=receipt.target_resource_usage,
                construction_resource_usage=receipt.construction_resource_usage,
                _token=object(),
            )
        self.assertIs(receipt_error.exception.outcome, OutcomeClass.MISSING_DEPENDENCY)


if __name__ == "__main__":
    unittest.main()
