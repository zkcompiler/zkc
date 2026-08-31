from __future__ import annotations

from dataclasses import replace
from itertools import product
from pathlib import Path
import re
import sys
import unittest
from urllib.parse import unquote


PACKAGE = Path(__file__).resolve().parents[1]
REPOSITORY = PACKAGE.parents[1]
DURABLE_PAGES = tuple(
    sorted(
        path
        for path in (REPOSITORY / "docs-next").rglob("*.md")
        if "notes" not in path.relative_to(REPOSITORY / "docs-next").parts
        or path == REPOSITORY / "docs-next/notes/README.md"
    )
)
sys.path.insert(0, str(PACKAGE))

import independent  # noqa: E402
import reference_model as m  # noqa: E402


class RunGroundingBasisTest(unittest.TestCase):
    def basis(self, qualification: m.RunQualification) -> m.ExecutionBasis:
        return m.ExecutionBasis(
            "protocol",
            object(),
            object(),
            qualification,
            object(),
        )

    def assert_agreement(
        self,
        public: object | None,
        private: tuple[m.ConfidentialRunCapability, ...],
    ) -> m.Result:
        primary = m.check_run_grounding_basis(public, private)
        secondary = independent.check_run_grounding_basis(public, private)
        self.assertEqual(primary, secondary)
        return primary

    def test_public_and_multiple_material_operands_require_one_exact_basis(
        self,
    ) -> None:
        basis = self.basis(m.RunQualification.CAUSAL)
        result = self.assert_agreement(
            m.issue_public_run_authority(basis),
            (
                m.issue_confidential_run_capability("oracle-0", basis),
                m.issue_confidential_run_capability("oracle-1", basis),
            ),
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)

    def test_equal_looking_distinct_run_is_refused_before_value_comparison(
        self,
    ) -> None:
        first = self.basis(m.RunQualification.CAUSAL)
        second = m.ExecutionBasis(
            first.protocol,
            first.invocation,
            first.completed_record,
            first.qualification,
            first.qualification_authority,
        )
        result = self.assert_agreement(
            m.issue_public_run_authority(first),
            (m.issue_confidential_run_capability("oracle-0", second),),
        )
        self.assertIs(result.outcome, m.Outcome.REFUSED)

    def test_material_cannot_use_replay_basis(self) -> None:
        basis = self.basis(m.RunQualification.REPLAY)
        result = self.assert_agreement(
            m.issue_public_run_authority(basis),
            (m.issue_confidential_run_capability("oracle-0", basis),),
        )
        self.assertIs(result.outcome, m.Outcome.REFUSED)

    def test_material_only_basis_is_derived_from_first_canonical_coordinate(
        self,
    ) -> None:
        basis = self.basis(m.RunQualification.CAUSAL)
        result = self.assert_agreement(
            None,
            (
                m.issue_confidential_run_capability("a", basis),
                m.issue_confidential_run_capability("b", basis),
            ),
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        malformed = self.assert_agreement(
            None,
            (
                m.issue_confidential_run_capability("b", basis),
                m.issue_confidential_run_capability("a", basis),
            ),
        )
        self.assertIs(malformed.outcome, m.Outcome.MALFORMED)


class EndpointSupportTest(unittest.TestCase):
    def test_primary_and_independent_classifiers_agree_on_full_matrix(self) -> None:
        for values in product(
            tuple(m.ChallengeMode),
            tuple(m.EndpointPurpose),
            tuple(m.ConstructionFamily),
            (False, True),
            (False, True),
            (False, True),
            (False, True),
            (False, True),
            (0, 1),
        ):
            (
                mode,
                purpose,
                family,
                oracle,
                effect,
                plan,
                realizes_present,
                realizes,
                arms,
            ) = values
            request = m.EndpointRequest(
                mode,
                purpose,
                family if mode is m.ChallengeMode.FIAT_SHAMIR else None,
                oracle,
                effect,
                plan,
                realizes_present,
                realizes,
                arms,
            )
            with self.subTest(request=request):
                self.assertEqual(
                    m.classify_endpoint_support(request),
                    independent.classify_endpoint_support(request),
                )

    def test_unsupported_family_dispatch_precedes_continuation_derivation(
        self,
    ) -> None:
        request = m.EndpointRequest(
            m.ChallengeMode.FIAT_SHAMIR,
            m.EndpointPurpose.CONTINUATION_PROVER,
            m.ConstructionFamily.DUPLEX_SPONGE,
            False,
            False,
            True,
            True,
            True,
            0,
        )
        result = m.classify_endpoint_support(request)
        self.assertEqual(
            result,
            m.Result(
                m.Outcome.UNSUPPORTED,
                ("OtherTranscriptConstructionFamily",),
            ),
        )

    def test_feature_reasons_are_exhaustive_and_canonical(self) -> None:
        request = m.EndpointRequest(
            m.ChallengeMode.FRESH,
            m.EndpointPurpose.GENERIC_PROVER,
            None,
            True,
            True,
            False,
            False,
            False,
            0,
        )
        self.assertEqual(
            m.classify_endpoint_support(request).reasons,
            (
                "FreshEndpoint",
                "GenericProverEndpoint",
                "StandardOracleEndpoint",
                "ModuleEffectEndpoint",
            ),
        )

    def test_affirmative_path_requires_the_exact_canonical_family(self) -> None:
        for family in (
            m.ConstructionFamily.DUPLEX_SPONGE,
            m.ConstructionFamily.OTHER_AUTHENTICATED,
        ):
            with self.subTest(family=family):
                request = m.EndpointRequest(
                    m.ChallengeMode.FIAT_SHAMIR,
                    m.EndpointPurpose.VERIFIER,
                    family,
                    False,
                    False,
                    False,
                    False,
                    False,
                    0,
                )
                self.assertEqual(
                    m.classify_endpoint_support(request),
                    m.Result(
                        m.Outcome.UNSUPPORTED,
                        ("OtherTranscriptConstructionFamily",),
                    ),
                )

    def test_plan_phase_preserves_missing_refused_and_malformed(self) -> None:
        base = m.EndpointRequest(
            m.ChallengeMode.FIAT_SHAMIR,
            m.EndpointPurpose.PLAN_PROVER,
            m.ConstructionFamily.CANONICAL_FRAMED,
            False,
            False,
            True,
            True,
            True,
            1,
        )
        self.assertIs(
            m.classify_endpoint_support(replace(base, plan_present=False)).outcome,
            m.Outcome.MISSING_DEPENDENCY,
        )
        self.assertIs(
            m.classify_endpoint_support(
                replace(base, plan_realizes_present=False)
            ).outcome,
            m.Outcome.MISSING_DEPENDENCY,
        )
        self.assertIs(
            m.classify_endpoint_support(replace(base, plan_realizes=False)).outcome,
            m.Outcome.REFUSED,
        )
        verifier = replace(base, purpose=m.EndpointPurpose.VERIFIER)
        self.assertIs(
            m.classify_endpoint_support(verifier).outcome,
            m.Outcome.MALFORMED,
        )


class AnalysisContractTest(unittest.TestCase):
    def verifier_bounds(self) -> m.VerifierBounds:
        return m.VerifierBounds(
            maximum_setup_roles=1,
            maximum_context_roles=1,
            exact_claim_count=1,
            maximum_setup_bytes=32,
            maximum_context_bytes=32,
            maximum_claim_group_bytes=96,
            maximum_evidence_bytes=64,
            maximum_schedule_constraints=2,
            maximum_group_check_steps=100,
            maximum_opening_check_steps=200,
            maximum_canonical_body_bytes=100,
        )

    def commitment_profile(self) -> m.CommitmentProfile:
        bounds = self.verifier_bounds()
        return m.CommitmentProfile(
            setup_role_ordinals=(0,),
            context_role_ordinals=(0,),
            role_types_valid=True,
            claim_count=1,
            schedule_atoms=("claim", "evidence", "check"),
            schedule_edges=(("claim", "evidence"), ("evidence", "check")),
            algorithms=m.EXPECTED_COMMITMENT_ALGORITHMS,
            declared_bounds=bounds,
            derived_bounds=bounds,
            required_bounds=bounds,
            canonical_body_bytes=100,
        )

    def test_counterfactual_rights_are_closed_and_denoted(self) -> None:
        accepted = m.admit_counterfactual_rights(
            (
                m.CounterfactualRight.PROGRAM_SIBLING,
                m.CounterfactualRight.RERUN,
            ),
            ("program-sibling", "root-rerun"),
        )
        self.assertIs(accepted.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(
            m.admit_counterfactual_rights(("Program",), ("program-sibling",)).outcome,
            m.Outcome.REFUSED,
        )
        self.assertIs(
            m.admit_counterfactual_rights(
                (m.CounterfactualRight.RERUN,), ("program-sibling",)
            ).outcome,
            m.Outcome.REFUSED,
        )

    def test_transport_projection_retains_owner_contract_references(self) -> None:
        owner = "analysis-property-profile"
        partition = m.common_failure_partition_ref(owner)
        self.assertEqual(
            partition.body,
            (
                "Unsupported",
                "MissingDependency",
                "CannotAnswer",
                "KindMismatch",
                "Refused",
                "Malformed",
                "DeterministicLimitExceeded",
                "CheckerFailure",
            ),
        )
        catalog = {
            "TheoremTruth": m.FamilyContract(
                "truth-subject",
                "truth-question",
                "truth-conclusion",
                "finite-cover-contract",
                partition,
            ),
            "TheoremApplicability": m.FamilyContract(
                "applicability-subject",
                "applicability-question",
                "applicability-conclusion",
                None,
                partition,
            ),
        }
        projection = m.transport_family_projection(
            owner, catalog, ("TheoremTruth", "TheoremApplicability")
        )
        self.assertEqual(
            projection,
            (
                m.FamilyContractRef(owner, "TheoremTruth"),
                m.FamilyContractRef(owner, "TheoremApplicability"),
            ),
        )
        self.assertEqual(
            catalog[projection[0].family].finite_cover_discharge_contract,
            "finite-cover-contract",
        )
        copied = replace(
            catalog["TheoremTruth"],
            failure_partition=m.FailurePartitionRef(
                owner, m.COMMON_FAILURE_PARTITION[:-1]
            ),
        )
        with self.assertRaisesRegex(ValueError, "failure partition"):
            m.transport_family_projection(
                owner,
                {**catalog, "TheoremTruth": copied},
                ("TheoremTruth",),
            )

    def test_commitment_profile_has_one_producer_for_every_formation_defect(
        self,
    ) -> None:
        profile = self.commitment_profile()
        self.assertIs(
            m.admit_commitment_profile(profile).outcome, m.Outcome.AFFIRMATIVE
        )

        first_algorithm = profile.algorithms[0]
        insufficient = replace(profile.declared_bounds, maximum_setup_roles=0)
        cycle_bounds = replace(profile.declared_bounds, maximum_schedule_constraints=3)
        mutations = {
            "SetupRoleOrdinalMismatch": replace(profile, setup_role_ordinals=(1,)),
            "ContextRoleOrdinalMismatch": replace(profile, context_role_ordinals=(1,)),
            "RoleTypeMismatch": replace(profile, role_types_valid=False),
            "ScheduleAtomMismatch": replace(
                profile, schedule_atoms=("claim", "claim", "check")
            ),
            "ScheduleCycle": replace(
                profile,
                schedule_edges=(
                    ("claim", "evidence"),
                    ("evidence", "check"),
                    ("check", "claim"),
                ),
                declared_bounds=cycle_bounds,
                derived_bounds=cycle_bounds,
            ),
            "AlgorithmABIMismatch": replace(
                profile,
                algorithms=(
                    replace(first_algorithm, output_abi="WrongOutput"),
                    *profile.algorithms[1:],
                ),
            ),
            "AlgorithmCompletedFailureRowNonempty": replace(
                profile,
                algorithms=(
                    replace(first_algorithm, completed_failure_row=("failure",)),
                    *profile.algorithms[1:],
                ),
            ),
            "IntrinsicBoundMismatch": replace(
                profile,
                derived_bounds=replace(profile.derived_bounds, maximum_setup_bytes=33),
            ),
            "IntrinsicBoundInsufficient": replace(
                profile, declared_bounds=insufficient, derived_bounds=insufficient
            ),
            "CanonicalBodyBoundExceeded": replace(profile, canonical_body_bytes=101),
        }
        self.assertEqual(tuple(mutations), m.COMMITMENT_DEFECT_ORDER)
        for expected, candidate in mutations.items():
            with self.subTest(expected=expected):
                self.assertEqual(
                    m.admit_commitment_profile(candidate),
                    m.Result(m.Outcome.NEGATIVE, (expected,)),
                )

    def test_commitment_profile_reports_all_defects_in_declared_order(self) -> None:
        profile = self.commitment_profile()
        insufficient = replace(profile.declared_bounds, maximum_setup_roles=0)
        candidate = replace(
            profile,
            setup_role_ordinals=(1,),
            context_role_ordinals=(1,),
            role_types_valid=False,
            schedule_edges=(("claim", "unknown"),),
            algorithms=(
                replace(
                    profile.algorithms[0],
                    output_abi="WrongOutput",
                    completed_failure_row=("failure",),
                ),
                *profile.algorithms[1:],
            ),
            declared_bounds=insufficient,
            derived_bounds=replace(insufficient, maximum_setup_bytes=33),
            canonical_body_bytes=101,
        )
        self.assertEqual(
            m.admit_commitment_profile(candidate),
            m.Result(
                m.Outcome.NEGATIVE,
                tuple(
                    tag for tag in m.COMMITMENT_DEFECT_ORDER if tag != "ScheduleCycle"
                ),
            ),
        )


class DuplexMaterialTest(unittest.TestCase):
    def candidate(self) -> m.DuplexMaterialCandidate:
        return m.DuplexMaterialCandidate(True, True, m.SaltCarrierState.EXACT, False)

    def test_exact_material_is_prepared_before_execution(self) -> None:
        self.assertEqual(
            m.prepare_duplex_material(self.candidate()),
            m.Result(m.Outcome.AFFIRMATIVE),
        )

    def test_refusal_reasons_are_exhaustive_and_canonical(self) -> None:
        candidate = m.DuplexMaterialCandidate(
            False, False, m.SaltCarrierState.SHORT_WITHIN_CAPACITY, True
        )
        self.assertEqual(
            m.prepare_duplex_material(candidate),
            m.Result(
                m.Outcome.REFUSED,
                tuple(reason.value for reason in m.DuplexMaterialRefusal),
            ),
        )

    def test_kind_mismatch_precedes_semantic_refusal_collection(self) -> None:
        candidate = m.DuplexMaterialCandidate(
            False, False, m.SaltCarrierState.WRONG_CARRIER_TYPE, True
        )
        self.assertEqual(
            m.prepare_duplex_material(candidate),
            m.Result(m.Outcome.KIND_MISMATCH),
        )

    def test_sequence_exceeding_declared_capacity_is_malformed(self) -> None:
        candidate = m.DuplexMaterialCandidate(
            True, True, m.SaltCarrierState.EXCEEDS_DECLARED_CAPACITY, False
        )
        self.assertEqual(
            m.prepare_duplex_material(candidate),
            m.Result(m.Outcome.MALFORMED),
        )

    def test_foreign_construction_key_has_one_key_set_reason(self) -> None:
        candidate = m.DuplexMaterialCandidate(
            True, False, m.SaltCarrierState.EXACT, False
        )
        self.assertEqual(
            m.prepare_duplex_material(candidate),
            m.Result(m.Outcome.REFUSED, ("MaterialKeySetMismatch",)),
        )


class DuplexInstanceEncodingTest(unittest.TestCase):
    def exact_case(
        self,
    ) -> tuple[tuple[m.DuplexInstanceBinding, ...], tuple[m.PublicInputDatum, ...]]:
        bindings = (
            m.DuplexInstanceBinding(
                2, m.InstanceValueOrigin.PUBLIC_INPUT, 0, b"field-element"
            ),
            m.DuplexInstanceBinding(
                5, m.InstanceValueOrigin.PUBLIC_INPUT, 1, b"field-element"
            ),
        )
        values = (
            m.PublicInputDatum(b"field-element", b"same-value"),
            m.PublicInputDatum(b"field-element", b"same-value"),
        )
        return bindings, values

    def test_two_reconstructors_emit_one_explicit_record_encoding(self) -> None:
        bindings, values = self.exact_case()
        primary = m.encode_duplex_instance(bindings, values)
        secondary = independent.encode_duplex_instance(bindings, values)
        self.assertEqual(primary, secondary)
        self.assertIs(primary.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(primary.encoded[:1], b"S")
        self.assertEqual(primary.encoded.count(b"R"), 2)
        self.assertEqual(primary.encoded.count(b"same-value"), 2)

    def test_non_public_statement_origin_is_refused_before_encoding(self) -> None:
        bindings, values = self.exact_case()
        candidate = (
            replace(bindings[0], origin=m.InstanceValueOrigin.CONSTANT),
            bindings[1],
        )
        self.assertEqual(
            m.encode_duplex_instance(candidate, values),
            m.InstanceEncodingResult(m.Outcome.REFUSED),
        )

    def test_missing_input_and_wrong_type_are_routed_before_bytes_exist(self) -> None:
        bindings, values = self.exact_case()
        missing = (replace(bindings[0], public_input_ref=9), bindings[1])
        wrong_type = (
            replace(bindings[0], value_type_body=b"wrong-type"),
            bindings[1],
        )
        self.assertEqual(
            m.encode_duplex_instance(missing, values),
            m.InstanceEncodingResult(m.Outcome.MISSING_DEPENDENCY),
        )
        self.assertEqual(
            m.encode_duplex_instance(wrong_type, values),
            m.InstanceEncodingResult(m.Outcome.KIND_MISMATCH),
        )


class FSConstructionDefectTest(unittest.TestCase):
    def affirmative_candidate(self) -> m.FSConstructionComparison:
        return m.FSConstructionComparison(
            *(True for _ in m.FS_CONSTRUCTION_DEFECT_ORDER)
        )

    def test_each_declared_defect_has_an_exact_producing_comparison(self) -> None:
        affirmative = self.affirmative_candidate()
        self.assertEqual(
            m.check_fs_construction_comparison(affirmative),
            m.Result(m.Outcome.AFFIRMATIVE),
        )
        fields = tuple(affirmative.__dataclass_fields__)
        self.assertEqual(len(fields), len(m.FS_CONSTRUCTION_DEFECT_ORDER))
        for field, expected in zip(fields, m.FS_CONSTRUCTION_DEFECT_ORDER):
            with self.subTest(expected=expected):
                candidate = replace(affirmative, **{field: False})
                self.assertEqual(
                    m.check_fs_construction_comparison(candidate),
                    m.Result(m.Outcome.NEGATIVE, (expected,)),
                )

    def test_multiple_comparison_failures_retain_declared_order(self) -> None:
        candidate = m.FSConstructionComparison(
            False, False, False, False, False, False, False, False
        )
        self.assertEqual(
            m.check_fs_construction_comparison(candidate),
            m.Result(m.Outcome.NEGATIVE, m.FS_CONSTRUCTION_DEFECT_ORDER),
        )

    def test_zero_challenge_core_is_ineligible_for_both_fs_families(self) -> None:
        for family in m.SUPPORTED_CONSTRUCTION_FAMILIES:
            with self.subTest(family=family):
                self.assertEqual(
                    m.admit_fiat_shamir_family_shape(family, 0),
                    m.Result(m.Outcome.REFUSED, ("EmptyChallengeDomain",)),
                )
                self.assertEqual(
                    m.admit_fiat_shamir_family_shape(family, 1),
                    m.Result(m.Outcome.AFFIRMATIVE),
                )
        self.assertEqual(
            m.admit_fiat_shamir_family_shape(
                m.ConstructionFamily.OTHER_AUTHENTICATED, 1
            ),
            m.Result(
                m.Outcome.UNSUPPORTED,
                ("OtherTranscriptConstructionFamily",),
            ),
        )


class DurablePageGuardTest(unittest.TestCase):
    PAGES = (
        "docs-next/analysis/analysis-model.md",
        "docs-next/analysis/cryptographic-properties.md",
        "docs-next/analysis/transport-composition-and-replay.md",
        "docs-next/pir/commitment-opening-verification.md",
        "docs-next/pir/duplex-sponge-fiat-shamir.md",
        "docs-next/pir/fiat-shamir.md",
        "docs-next/pir/interactive-core.md",
        "docs-next/pir/interfaces-and-plans.md",
        "docs-next/pir/oracle-commitment-construction.md",
        "docs-next/pir/endpoint-projection-views.md",
        "docs-next/compiler/compiler-model.md",
        "docs-next/compiler/assessment-selection-and-replay.md",
        "docs-next/realization/README.md",
        "docs-next/relations/protocol-correspondence.md",
        "docs-next/relations/relation-model.md",
    )

    def test_retired_undefined_tokens_and_prose_aliases_are_absent(self) -> None:
        corpus = "\n".join((REPOSITORY / path).read_text() for path in self.PAGES)
        for forbidden in (
            "BoundedSymbol",
            "TypedFailureCoordinate",
            "common K3-C outcome partition",
            "common K3-C source-ingress failure partition",
            "common Analysis qualified-outcome partition",
            "CanonicalSortedUniqueSeq<Rerun | Fork | Rewind | Program>",
            "DuplexFinalRoundMismatch",
            "supports only the rewinding state-restoration route",
            "K1SemanticReference",
            "ProtocolConstructionMismatch",
            "InvocationProtocolMismatch",
        ):
            with self.subTest(forbidden=forbidden):
                self.assertNotIn(forbidden, corpus)

        commitment_page = (
            REPOSITORY / "docs-next/pir/commitment-opening-verification.md"
        ).read_text()
        self.assertNotIn("exact_failure_catalog", commitment_page)
        oracle_page = (
            REPOSITORY / "docs-next/pir/oracle-commitment-construction.md"
        ).read_text()
        self.assertNotIn("exact_failure_catalog", oracle_page)

    def test_repaired_owner_laws_are_closed_in_their_canonical_homes(self) -> None:
        foundation = (
            REPOSITORY / "docs-next/foundation/executable-foundations.md"
        ).read_text()
        endpoint = (
            REPOSITORY / "docs-next/pir/endpoint-projection-views.md"
        ).read_text()
        relations = (
            REPOSITORY / "docs-next/relations/protocol-correspondence.md"
        ).read_text()
        analysis = (REPOSITORY / "docs-next/analysis/analysis-model.md").read_text()
        properties = (
            REPOSITORY / "docs-next/analysis/cryptographic-properties.md"
        ).read_text()

        self.assertIn("ExactMapBody(m,KeyBody,ValueBody)", foundation)
        self.assertIn("ExactMapOver<D,V>", foundation)
        self.assertIn("DispatchEndpointTranscriptConstruction", endpoint)
        self.assertIn("OtherTranscriptConstructionFamily", endpoint)
        self.assertNotIn("| Construction owner profile |", endpoint)
        self.assertNotRegex(endpoint, r"\bTranscriptConstructionProfile\(")
        self.assertIn(
            "FoundationSameTypeEquality(relation_material,pir_material) = true",
            relations,
        )
        self.assertNotIn("terminal-completion RunRecord object", relations)
        self.assertNotIn("RelationRunView capabilities", relations)
        self.assertIn("TotalAnalysisLawSignature<P,Inputs,Output>", analysis)
        self.assertIn("MissingDependency(absent exact authenticated dependency)", analysis)
        self.assertIn("KindMismatch(wrong exact owner, profile, regime", analysis)
        self.assertIn("exact root-rerun interface required", properties)

    def test_formal_symbols_use_semantic_owner_names(self) -> None:
        corpus = "\n".join(path.read_text() for path in DURABLE_PAGES)
        for forbidden in (
            "K1BooleanDatum",
            "K1Equal",
            "K1EnvelopeForAnalysisContract",
            "K2ReadOf",
            "K2RoleSemanticClosure",
            "K2FrameCoordinate",
            "K2ProverReadCoordinate",
            "K3DProjectionRelationProfile",
            "k2_check_ref",
            "k2_accept_terminal_ref",
            "K1-HASH-BINDING-CONFLICT",
        ):
            with self.subTest(forbidden=forbidden):
                self.assertNotIn(forbidden, corpus)

        foundation = (
            REPOSITORY / "docs-next/foundation/executable-foundations.md"
        ).read_text()
        endpoint = (
            REPOSITORY / "docs-next/pir/endpoint-projection-views.md"
        ).read_text()
        self.assertIn("MetaBooleanDatum(false)", foundation)
        self.assertIn("CanonicalValueEqual_T(x,y)", foundation)
        self.assertIn("ProtocolRoleSemanticClosure", endpoint)
        self.assertIn("ProtocolFrameCoordinate", endpoint)

    def test_all_durable_markdown_fences_are_balanced(self) -> None:
        for absolute_path in DURABLE_PAGES:
            path = absolute_path.relative_to(REPOSITORY)
            text = absolute_path.read_text()
            with self.subTest(path=str(path)):
                opened: str | None = None
                for line_number, line in enumerate(text.splitlines(), start=1):
                    stripped = line.strip()
                    marker = (
                        "```"
                        if stripped.startswith("```")
                        else "~~~"
                        if stripped.startswith("~~~")
                        else None
                    )
                    if marker is None:
                        continue
                    if opened is None:
                        opened = marker
                    else:
                        self.assertEqual(
                            stripped,
                            marker,
                            f"nested or mismatched fence at {path}:{line_number}",
                        )
                        opened = None
                self.assertIsNone(opened, f"unclosed fence in {path}")

    def test_durable_manifest_is_an_exact_nonduplicated_inventory(self) -> None:
        manifest_path = REPOSITORY / "docs-next/project/documentation-manifest.md"
        entries: list[Path] = []
        for line in manifest_path.read_text().splitlines():
            if not line.startswith("| [`"):
                continue
            match = re.match(r"\| \[`([^`]+\.md)`\]\(([^)]+)\)", line)
            self.assertIsNotNone(match, f"malformed manifest row: {line}")
            assert match is not None
            target = (manifest_path.parent / unquote(match.group(2))).resolve()
            entries.append(target)
        self.assertEqual(len(entries), len(set(entries)), "duplicate manifest entry")
        self.assertEqual(tuple(sorted(entries)), DURABLE_PAGES)

    def test_every_local_markdown_file_target_exists(self) -> None:
        pattern = re.compile(r"(?<!!)\[[^\]]*\]\(([^)]+)\)")
        for page in DURABLE_PAGES:
            for raw_target in pattern.findall(page.read_text()):
                target = raw_target.strip()
                if target.startswith(("#", "http://", "https://", "mailto:")):
                    continue
                if target.startswith("<") and target.endswith(">"):
                    target = target[1:-1]
                target = unquote(target.split("#", 1)[0])
                if not target or not target.endswith(".md"):
                    continue
                resolved = (page.parent / target).resolve()
                with self.subTest(
                    page=str(page.relative_to(REPOSITORY)), target=target
                ):
                    self.assertTrue(
                        resolved.exists(), f"missing local target {resolved}"
                    )


if __name__ == "__main__":
    unittest.main()
