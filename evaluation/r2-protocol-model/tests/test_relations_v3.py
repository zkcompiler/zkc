from __future__ import annotations

from dataclasses import fields, replace
from pathlib import Path
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = MODEL_ROOT.parents[1]
sys.path.insert(0, str(MODEL_ROOT))

from r2model.execution import (
    ExecutionRecord,
    QualifiedExecution,
    coupled_fresh_tape,
    execute,
    qualify_execution,
)
from r2model.frigrind import (
    ApplicationContext,
    CoreDerivationKind,
    DEFAULT_RESOURCE_PLAN,
    ExecutionRequest,
    FixedNoncePlan,
    FreshTapeOrigin,
    ValueSort,
    base_scenario,
    build_evaluator_basis,
    fresh_fri_scenario,
    fresh_grinding_scenario,
    load_fixture,
    load_external_fresh,
    load_invocation,
)
from r2model.relations import (
    AnchorCapability,
    AnchorReadRequest,
    DispositionKind,
    HybridFactorization,
    PointwiseBridge,
    ProtocolStatementOccurrence,
    RelationPublicValue,
    RelationRunEvidence,
    RelationShape,
    SubjectOrganization,
    ValidationProfile,
    check_anchor_authority,
    check_hybrid_factorization,
    check_pointwise_bridge,
    check_typed_disposition_map,
    classify_projection,
    compare_full_observations,
    compare_mapped_values,
    compare_origins,
    compare_strategies,
    derive_hybrid_factorization,
    derive_pointwise_bridge,
    derive_relation_shape,
    derive_relation_run_evidence,
    derive_validation_profile,
    project_sha256_216,
    projection_loss_applicability,
    protocol_statement_occurrence,
    statement_correspondence,
)
from r2model.terms import CheckResult, OutcomeClass, semantic_id


class RelationsV3Test(unittest.TestCase):
    """Cold-boundary tests for replay-qualified, Core-derived relations."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = load_fixture(REPO_ROOT)
        cls.companion = load_fixture(REPO_ROOT, companion=True)
        cls.invocation = load_invocation(REPO_ROOT)
        cls.fs_scenario = base_scenario(cls.fixture)
        cls.fresh_grinding = fresh_grinding_scenario(cls.fs_scenario)
        cls.fresh_fri = fresh_fri_scenario(cls.fs_scenario)
        cls.application_context = ApplicationContext(
            "zkc.r2.frigrind",
            "canonical-execution",
        )
        cls.basis = build_evaluator_basis(
            REPO_ROOT,
            {
                cls.fs_scenario.construction.identity,
                cls.fresh_grinding.construction.identity,
                cls.fresh_fri.construction.identity,
            },
        )
        source_fixture_id = f"sha256:{cls.fixture.sha256}"
        source_package_id = cls.invocation.identity

        cls.fs_request = ExecutionRequest(
            cls.fs_scenario,
            cls.invocation.input_bundle,
            cls.application_context,
            cls.basis.identity,
            DEFAULT_RESOURCE_PLAN,
            CoreDerivationKind.FIXTURE_GRINDING_CORE,
            source_fixture_id,
            source_package_id,
            nonce_search=cls.invocation.default_search,
        )
        cls.fs_record = cls._record(execute(cls.fs_request, cls.basis))
        cls.fs_qualified = cls._qualified(
            qualify_execution(cls.fs_request, cls.basis, cls.fs_record)
        )
        fs_nonce = cls.fs_record.prover_value("nonce")

        external_tape, external_nonce = load_external_fresh(
            REPO_ROOT,
            cls.fresh_grinding.core,
        )
        cls.external_request = ExecutionRequest(
            cls.fresh_grinding,
            cls.invocation.input_bundle,
            cls.application_context,
            cls.basis.identity,
            DEFAULT_RESOURCE_PLAN,
            CoreDerivationKind.FIXTURE_GRINDING_CORE,
            source_fixture_id,
            source_package_id,
            fixed_nonce=external_nonce,
            coin_tape=external_tape,
        )
        cls.external_record = cls._record(execute(cls.external_request, cls.basis))
        cls.external_qualified = cls._qualified(
            qualify_execution(
                cls.external_request,
                cls.basis,
                cls.external_record,
            )
        )

        grinding_tape = coupled_fresh_tape(
            cls.fs_qualified,
            cls.fresh_grinding.core,
        )
        if isinstance(grinding_tape, CheckResult):
            raise AssertionError(grinding_tape)
        cls.grinding_tape = grinding_tape
        cls.coupled_grinding_request = ExecutionRequest(
            cls.fresh_grinding,
            cls.invocation.input_bundle,
            cls.application_context,
            cls.basis.identity,
            DEFAULT_RESOURCE_PLAN,
            CoreDerivationKind.FIXTURE_GRINDING_CORE,
            source_fixture_id,
            source_package_id,
            fixed_nonce=FixedNoncePlan(fs_nonce),
            coin_tape=grinding_tape,
        )
        cls.coupled_grinding_record = cls._record(
            execute(
                cls.coupled_grinding_request,
                cls.basis,
                (cls.fs_qualified,),
            )
        )
        cls.coupled_grinding_qualified = cls._qualified(
            qualify_execution(
                cls.coupled_grinding_request,
                cls.basis,
                cls.coupled_grinding_record,
                (cls.fs_qualified,),
            )
        )

        fri_tape = coupled_fresh_tape(cls.fs_qualified, cls.fresh_fri.core)
        if isinstance(fri_tape, CheckResult):
            raise AssertionError(fri_tape)
        cls.coupled_fri_request = ExecutionRequest(
            cls.fresh_fri,
            cls.invocation.input_bundle,
            cls.application_context,
            cls.basis.identity,
            DEFAULT_RESOURCE_PLAN,
            CoreDerivationKind.DROP_GRINDING_PROJECTION,
            source_fixture_id,
            source_package_id,
            coin_tape=fri_tape,
        )
        cls.coupled_fri_record = cls._record(
            execute(cls.coupled_fri_request, cls.basis, (cls.fs_qualified,))
        )
        cls.coupled_fri_qualified = cls._qualified(
            qualify_execution(
                cls.coupled_fri_request,
                cls.basis,
                cls.coupled_fri_record,
                (cls.fs_qualified,),
            )
        )

        cls.shared_shape = cls._shape(
            derive_relation_shape(cls.fresh_grinding, cls.fs_scenario)
        )
        cls.shared_profile = cls._profile(
            derive_validation_profile(
                cls.shared_shape,
                cls.coupled_grinding_qualified,
                cls.fs_qualified,
            )
        )
        cls.external_profile = cls._profile(
            derive_validation_profile(
                cls.shared_shape,
                cls.external_qualified,
                cls.fs_qualified,
            )
        )
        cls.distinct_shape = cls._shape(
            derive_relation_shape(cls.fresh_fri, cls.fs_scenario)
        )
        cls.distinct_profile = cls._profile(
            derive_validation_profile(
                cls.distinct_shape,
                cls.coupled_fri_qualified,
                cls.fs_qualified,
            )
        )
        cls.hybrid = cls._hybrid(
            derive_hybrid_factorization(
                cls.distinct_shape,
                cls.distinct_profile,
                cls.coupled_fri_qualified,
                cls.fs_qualified,
            )
        )

    @staticmethod
    def _record(value: ExecutionRecord | CheckResult) -> ExecutionRecord:
        if isinstance(value, CheckResult):
            raise AssertionError(value)
        if not isinstance(value, ExecutionRecord):
            raise AssertionError(type(value))
        return value

    @staticmethod
    def _qualified(value: QualifiedExecution | CheckResult) -> QualifiedExecution:
        if isinstance(value, CheckResult):
            raise AssertionError(value)
        if not isinstance(value, QualifiedExecution):
            raise AssertionError(type(value))
        return value

    @staticmethod
    def _shape(value: RelationShape | CheckResult) -> RelationShape:
        if isinstance(value, CheckResult):
            raise AssertionError(value)
        if not isinstance(value, RelationShape):
            raise AssertionError(type(value))
        return value

    @staticmethod
    def _profile(value: ValidationProfile | CheckResult) -> ValidationProfile:
        if isinstance(value, CheckResult):
            raise AssertionError(value)
        if not isinstance(value, ValidationProfile):
            raise AssertionError(type(value))
        return value

    @staticmethod
    def _hybrid(value: HybridFactorization | CheckResult) -> HybridFactorization:
        if isinstance(value, CheckResult):
            raise AssertionError(value)
        if not isinstance(value, HybridFactorization):
            raise AssertionError(type(value))
        return value

    def assert_result(
        self,
        value: object,
        outcome: OutcomeClass,
        code: str | None = None,
    ) -> CheckResult:
        self.assertIsInstance(value, CheckResult)
        result = value
        assert isinstance(result, CheckResult)
        self.assertIs(result.outcome, outcome)
        if code is not None:
            self.assertEqual(result.code, code)
        return result

    @staticmethod
    def _run_evidence(result: CheckResult) -> RelationRunEvidence:
        evidence = result.evidence
        return RelationRunEvidence(
            evidence["relation_shape_id"],
            evidence["validation_profile_id"],
            evidence["fresh_qualification_id"],
            evidence["fs_qualification_id"],
            evidence["fresh_request_id"],
            evidence["fs_request_id"],
            evidence["fresh_record_id"],
            evidence["fs_record_id"],
            evidence["fresh_coin_tape_id"],
            tuple(evidence["fresh_dependency_qualification_ids"]),
            tuple(evidence["fs_dependency_qualification_ids"]),
        )

    def _equal_relation_operand(self) -> tuple[ProtocolStatementOccurrence, RelationPublicValue]:
        protocol = protocol_statement_occurrence(self.fs_qualified)
        self.assertIsInstance(protocol, ProtocolStatementOccurrence)
        assert isinstance(protocol, ProtocolStatementOccurrence)
        relation = RelationPublicValue(
            semantic_id("r2.forged-relation-subject", {}),
            protocol.occurrence,
            protocol.value_sort,
            protocol.cardinality,
            protocol.value,
            semantic_id("r2.forged-relation-evidence", {}),
        )
        return protocol, relation

    def test_shared_and_mapped_distinct_shapes_are_complete_core_derivations(self) -> None:
        self.assertIs(
            self.shared_shape.organization,
            SubjectOrganization.SHARED_GRINDING_CORE,
        )
        self.assertEqual(
            self.shared_shape.fresh_core_id,
            self.shared_shape.fs_core_id,
        )
        self.assertEqual(
            tuple(item.occurrence for item in self.shared_shape.fresh_actions),
            self.fresh_grinding.core.schedule,
        )
        self.assertEqual(
            tuple(item.occurrence for item in self.shared_shape.fs_actions),
            self.fs_scenario.core.schedule,
        )
        self.assertEqual(len(self.shared_shape.dispositions), len(self.fs_scenario.core.actions))
        self.assertTrue(
            all(
                item.kind is DispositionKind.PRESERVED
                for item in self.shared_shape.dispositions
            )
        )

        self.assertIs(
            self.distinct_shape.organization,
            SubjectOrganization.MAPPED_DISTINCT_CORES,
        )
        self.assertNotEqual(
            self.distinct_shape.fresh_core_id,
            self.distinct_shape.fs_core_id,
        )
        self.assertEqual(
            tuple(item.occurrence for item in self.distinct_shape.fresh_actions),
            self.fresh_fri.core.schedule,
        )
        self.assertEqual(
            tuple(item.occurrence for item in self.distinct_shape.fs_actions),
            self.fs_scenario.core.schedule,
        )
        self.assertEqual(
            sum(
                item.kind is DispositionKind.PRESERVED
                for item in self.distinct_shape.dispositions
            ),
            len(self.fresh_fri.core.actions),
        )
        self.assertEqual(
            sum(
                item.kind is DispositionKind.TARGET_ONLY
                for item in self.distinct_shape.dispositions
            ),
            len(self.fs_scenario.core.actions) - len(self.fresh_fri.core.actions),
        )

    def test_reusable_shape_and_profile_exclude_run_specific_identities(self) -> None:
        forbidden_fields = {
            "fresh_request_id",
            "fs_request_id",
            "fresh_record_id",
            "fs_record_id",
            "fresh_qualification_id",
            "fs_qualification_id",
            "fresh_coin_tape_id",
            "fresh_dependency_qualification_ids",
            "fs_dependency_qualification_ids",
            "projected_trace_id",
        }
        for reusable in (
            self.shared_shape,
            self.shared_profile,
            self.distinct_shape,
            self.distinct_profile,
        ):
            with self.subTest(reusable=type(reusable).__name__):
                names = {item.name for item in fields(reusable)}
                self.assertTrue(names.isdisjoint(forbidden_fields))

        dynamic_ids = {
            self.fs_request.identity,
            self.fs_record.identity,
            self.fs_qualified.identity,
            self.external_request.identity,
            self.external_record.identity,
            self.external_qualified.identity,
            self.coupled_grinding_request.identity,
            self.coupled_grinding_record.identity,
            self.coupled_grinding_qualified.identity,
            self.grinding_tape.identity,
            self.hybrid.projected_trace_id,
        }
        self.assertTrue(dynamic_ids.isdisjoint(vars(self.shared_profile).values()))
        self.assertTrue(dynamic_ids.isdisjoint(vars(self.distinct_profile).values()))

        # Run controls differ, but the reusable validation policy does not.
        self.assertNotEqual(
            self.external_qualified.identity,
            self.coupled_grinding_qualified.identity,
        )
        self.assertEqual(self.external_profile, self.shared_profile)
        self.assertEqual(self.external_profile.identity, self.shared_profile.identity)

    def test_complete_core_authority_rejects_co_truncation_and_swapped_order(self) -> None:
        for shape, profile, fresh in (
            (
                self.shared_shape,
                self.shared_profile,
                self.coupled_grinding_qualified,
            ),
            (
                self.distinct_shape,
                self.distinct_profile,
                self.coupled_fri_qualified,
            ),
        ):
            with self.subTest(organization=shape.organization.value):
                co_truncated = replace(
                    shape,
                    fresh_actions=shape.fresh_actions[:-1],
                    fs_actions=shape.fs_actions[:-1],
                    dispositions=shape.dispositions[:-1],
                )
                colluding_profile = replace(
                    profile,
                    relation_shape_id=co_truncated.identity,
                )
                self.assert_result(
                    check_typed_disposition_map(
                        co_truncated,
                        colluding_profile,
                        fresh,
                        self.fs_qualified,
                    ),
                    OutcomeClass.MISMATCH,
                    "R2-VALID-002",
                )

                swapped_actions = list(shape.fresh_actions)
                swapped_actions[0], swapped_actions[1] = (
                    swapped_actions[1],
                    swapped_actions[0],
                )
                swapped = replace(shape, fresh_actions=tuple(swapped_actions))
                colluding_profile = replace(
                    profile,
                    relation_shape_id=swapped.identity,
                )
                self.assert_result(
                    check_typed_disposition_map(
                        swapped,
                        colluding_profile,
                        fresh,
                        self.fs_qualified,
                    ),
                    OutcomeClass.MISMATCH,
                    "R2-VALID-002",
                )

    def test_coupled_runs_commute_for_values_observations_and_origins(self) -> None:
        judgments = (
            (compare_mapped_values, "R2-VALUE-000"),
            (compare_full_observations, "R2-OBS-000"),
            (compare_origins, "R2-ORIGIN-000"),
        )
        pairs = (
            (
                self.shared_shape,
                self.shared_profile,
                self.coupled_grinding_qualified,
            ),
            (
                self.distinct_shape,
                self.distinct_profile,
                self.coupled_fri_qualified,
            ),
        )
        for shape, profile, fresh in pairs:
            for judgment, code in judgments:
                with self.subTest(
                    organization=shape.organization.value,
                    judgment=judgment.__name__,
                ):
                    result = self.assert_result(
                        judgment(shape, profile, fresh, self.fs_qualified),
                        OutcomeClass.AFFIRMATIVE,
                        code,
                    )
                    evidence = self._run_evidence(result)
                    self.assertEqual(
                        evidence.identity,
                        result.evidence["run_evidence_id"],
                    )
                    self.assertEqual(
                        evidence.fresh_qualification_id,
                        fresh.identity,
                    )
                    self.assertEqual(
                        evidence.fs_qualification_id,
                        self.fs_qualified.identity,
                    )

        public_evidence = derive_relation_run_evidence(
            self.shared_shape,
            self.shared_profile,
            self.coupled_grinding_qualified,
            self.fs_qualified,
        )
        self.assertIsInstance(public_evidence, RelationRunEvidence)
        assert isinstance(public_evidence, RelationRunEvidence)
        map_result = check_typed_disposition_map(
            self.shared_shape,
            self.shared_profile,
            self.coupled_grinding_qualified,
            self.fs_qualified,
        )
        self.assertIsInstance(map_result, CheckResult)
        assert isinstance(map_result, CheckResult)
        self.assertEqual(
            public_evidence.identity,
            map_result.evidence["run_evidence_id"],
        )
        self.assertEqual(public_evidence, self._run_evidence(map_result))

    def test_strategy_contracts_are_semantically_negative(self) -> None:
        for shape, profile, fresh in (
            (
                self.shared_shape,
                self.shared_profile,
                self.coupled_grinding_qualified,
            ),
            (
                self.distinct_shape,
                self.distinct_profile,
                self.coupled_fri_qualified,
            ),
        ):
            with self.subTest(organization=shape.organization.value):
                result = self.assert_result(
                    compare_strategies(
                        shape,
                        profile,
                        fresh,
                        self.fs_qualified,
                    ),
                    OutcomeClass.SEMANTIC_NEGATIVE,
                    "R2-STRATEGY-001",
                )
                self.assertIn(
                    "message:nonce",
                    result.evidence["differing_occurrences"],
                )

    def test_hybrid_is_run_bound_and_requires_the_exact_fs_dependency(self) -> None:
        self.assertEqual(
            self.hybrid.fresh_qualification_id,
            self.coupled_fri_qualified.identity,
        )
        self.assertEqual(
            self.hybrid.fs_qualification_id,
            self.fs_qualified.identity,
        )
        self.assertEqual(
            self.coupled_fri_qualified.dependencies,
            (self.fs_qualified,),
        )
        self.assert_result(
            check_hybrid_factorization(
                self.hybrid,
                self.distinct_shape,
                self.distinct_profile,
                self.coupled_fri_qualified,
                self.fs_qualified,
            ),
            OutcomeClass.AFFIRMATIVE,
            "R2-HYBRID-000",
        )

        forged_factorization = replace(
            self.hybrid,
            fs_qualification_id=semantic_id("hostile.fs-qualification", {}),
        )
        self.assert_result(
            check_hybrid_factorization(
                forged_factorization,
                self.distinct_shape,
                self.distinct_profile,
                self.coupled_fri_qualified,
                self.fs_qualified,
            ),
            OutcomeClass.MISMATCH,
            "R2-HYBRID-005",
        )
        missing_link = replace(self.coupled_fri_qualified, dependencies=())
        result = derive_hybrid_factorization(
            self.distinct_shape,
            self.distinct_profile,
            missing_link,
            self.fs_qualified,
        )
        self.assertIsInstance(result, CheckResult)
        self.assertNotEqual(result.outcome, OutcomeClass.AFFIRMATIVE)

    def test_external_fresh_run_cannot_substitute_for_coupled_evidence(self) -> None:
        external_map = self.assert_result(
            check_typed_disposition_map(
                self.shared_shape,
                self.external_profile,
                self.external_qualified,
                self.fs_qualified,
            ),
            OutcomeClass.AFFIRMATIVE,
            "R2-MAP-000",
        )
        coupled_map = self.assert_result(
            check_typed_disposition_map(
                self.shared_shape,
                self.shared_profile,
                self.coupled_grinding_qualified,
                self.fs_qualified,
            ),
            OutcomeClass.AFFIRMATIVE,
            "R2-MAP-000",
        )
        external_evidence = self._run_evidence(external_map)
        coupled_evidence = self._run_evidence(coupled_map)
        self.assertIs(
            self.external_request.coin_tape.origin,
            FreshTapeOrigin.EXTERNAL_FIXTURE,
        )
        self.assertEqual(external_evidence.fresh_dependency_qualification_ids, ())
        self.assertEqual(
            coupled_evidence.fresh_dependency_qualification_ids,
            (self.fs_qualified.identity,),
        )
        self.assertNotEqual(external_evidence.identity, coupled_evidence.identity)
        self.assert_result(
            compare_mapped_values(
                self.shared_shape,
                self.external_profile,
                self.external_qualified,
                self.fs_qualified,
            ),
            OutcomeClass.MISMATCH,
            "R2-VALUE-001",
        )
        self.assert_result(
            derive_hybrid_factorization(
                self.shared_shape,
                self.external_profile,
                self.external_qualified,
                self.fs_qualified,
            ),
            OutcomeClass.MISMATCH,
            "R2-HYBRID-001",
        )

    def test_every_execution_consuming_judgment_requalifies(self) -> None:
        events = list(self.coupled_grinding_record.events)
        events[0] = replace(events[0], value=events[0].value + 1)
        forged_grinding = replace(
            self.coupled_grinding_qualified,
            record=replace(
                self.coupled_grinding_record,
                events=tuple(events),
            ),
        )
        fri_events = list(self.coupled_fri_record.events)
        fri_events[0] = replace(fri_events[0], value=fri_events[0].value + 1)
        forged_fri = replace(
            self.coupled_fri_qualified,
            record=replace(self.coupled_fri_record, events=tuple(fri_events)),
        )
        protocol, relation = self._equal_relation_operand()
        bridge = PointwiseBridge(relation, protocol)

        forged_calls = (
            lambda: derive_validation_profile(
                self.shared_shape,
                forged_grinding,
                self.fs_qualified,
            ),
            lambda: check_typed_disposition_map(
                self.shared_shape,
                self.shared_profile,
                forged_grinding,
                self.fs_qualified,
            ),
            lambda: compare_mapped_values(
                self.shared_shape,
                self.shared_profile,
                forged_grinding,
                self.fs_qualified,
            ),
            lambda: compare_full_observations(
                self.shared_shape,
                self.shared_profile,
                forged_grinding,
                self.fs_qualified,
            ),
            lambda: compare_origins(
                self.shared_shape,
                self.shared_profile,
                forged_grinding,
                self.fs_qualified,
            ),
            lambda: compare_strategies(
                self.shared_shape,
                self.shared_profile,
                forged_grinding,
                self.fs_qualified,
            ),
            lambda: derive_hybrid_factorization(
                self.distinct_shape,
                self.distinct_profile,
                forged_fri,
                self.fs_qualified,
            ),
            lambda: check_hybrid_factorization(
                self.hybrid,
                self.distinct_shape,
                self.distinct_profile,
                forged_fri,
                self.fs_qualified,
            ),
            lambda: derive_relation_run_evidence(
                self.shared_shape,
                self.shared_profile,
                forged_grinding,
                self.fs_qualified,
            ),
            lambda: protocol_statement_occurrence(
                replace(self.fs_qualified, record=replace(self.fs_record, events=()))
            ),
            lambda: derive_pointwise_bridge(
                relation,
                replace(self.fs_qualified, record=replace(self.fs_record, events=())),
            ),
            lambda: check_pointwise_bridge(
                bridge,
                replace(self.fs_qualified, record=replace(self.fs_record, events=())),
            ),
            lambda: statement_correspondence(
                replace(self.fs_qualified, record=replace(self.fs_record, events=())),
                relation,
            ),
        )
        for call in forged_calls:
            with self.subTest(call=call):
                result = call()
                self.assertIsInstance(result, CheckResult)
                assert isinstance(result, CheckResult)
                self.assertIsNot(result.outcome, OutcomeClass.AFFIRMATIVE)

        raw_calls = (
            lambda: derive_validation_profile(self.shared_shape, object(), self.fs_qualified),
            lambda: check_typed_disposition_map(
                self.shared_shape,
                self.shared_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: compare_mapped_values(
                self.shared_shape,
                self.shared_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: compare_full_observations(
                self.shared_shape,
                self.shared_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: compare_origins(
                self.shared_shape,
                self.shared_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: compare_strategies(
                self.shared_shape,
                self.shared_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: derive_hybrid_factorization(
                self.distinct_shape,
                self.distinct_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: check_hybrid_factorization(
                self.hybrid,
                self.distinct_shape,
                self.distinct_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: derive_relation_run_evidence(
                self.shared_shape,
                self.shared_profile,
                object(),
                self.fs_qualified,
            ),
            lambda: protocol_statement_occurrence(object()),
            lambda: derive_pointwise_bridge(relation, object()),
            lambda: check_pointwise_bridge(bridge, object()),
            lambda: statement_correspondence(object(), relation),
        )
        for call in raw_calls:
            with self.subTest(call=call):
                result = call()
                self.assertIsInstance(result, CheckResult)
                assert isinstance(result, CheckResult)
                self.assertIsNot(result.outcome, OutcomeClass.AFFIRMATIVE)

    def test_statement_correspondence_remains_missing_even_for_equal_syntax(self) -> None:
        protocol, relation = self._equal_relation_operand()
        self.assert_result(
            statement_correspondence(self.fs_qualified),
            OutcomeClass.MISSING_DEPENDENCY,
            "R2-BRIDGE-001",
        )
        self.assert_result(
            derive_pointwise_bridge(relation, self.fs_qualified),
            OutcomeClass.MISSING_DEPENDENCY,
            "R2-BRIDGE-009",
        )
        self.assert_result(
            statement_correspondence(self.fs_qualified, relation),
            OutcomeClass.MISSING_DEPENDENCY,
            "R2-BRIDGE-009",
        )
        self.assert_result(
            check_pointwise_bridge(
                PointwiseBridge(relation, protocol),
                self.fs_qualified,
            ),
            OutcomeClass.MISSING_DEPENDENCY,
            "R2-BRIDGE-009",
        )

    def test_anchor_authority_projection_and_loss_are_noncollapsed(self) -> None:
        for label in ("contract", "statement"):
            with self.subTest(label=label):
                result = self.assert_result(
                    check_anchor_authority(
                        self.fixture,
                        AnchorReadRequest(
                            label,
                            AnchorCapability.REFERENCE_VALUE,
                        ),
                    ),
                    OutcomeClass.AFFIRMATIVE,
                    "R2-AUTH-000",
                )
                limbs = project_sha256_216(result.evidence["anchor"])
                self.assertIsInstance(limbs, tuple)
                assert isinstance(limbs, tuple)
                self.assertEqual(len(limbs), 8)
                self.assertTrue(all(0 <= limb < 1 << 27 for limb in limbs))

        self.assert_result(
            check_anchor_authority(
                self.fixture,
                AnchorReadRequest(
                    "contract",
                    AnchorCapability.SEMANTIC_SOURCE_BYTES,
                ),
            ),
            OutcomeClass.REFUSED,
            "R2-AUTH-001",
        )
        self.assert_result(
            check_anchor_authority(
                self.fixture,
                AnchorReadRequest("absent", AnchorCapability.REFERENCE_VALUE),
            ),
            OutcomeClass.MISSING_DEPENDENCY,
            "R2-AUTH-004",
        )
        self.assert_result(
            classify_projection(self.fixture),
            OutcomeClass.NOT_EXERCISED,
            "R2-PROJ-000",
        )
        projected = self.assert_result(
            classify_projection(self.companion),
            OutcomeClass.AFFIRMATIVE,
            "R2-PROJ-002",
        )
        self.assertEqual(projected.evidence["input_bits"], 256)
        self.assertEqual(projected.evidence["output_bits"], 216)
        self.assertEqual(projected.evidence["truncated_bits"], 40)
        self.assert_result(
            projection_loss_applicability(self.fixture),
            OutcomeClass.NOT_EXERCISED,
            "R2-LOSS-000",
        )
        self.assert_result(
            projection_loss_applicability(self.companion),
            OutcomeClass.CANNOT_ANSWER,
            "R2-LOSS-001",
        )
        self.assert_result(
            project_sha256_216("SHA256:" + "0" * 64),
            OutcomeClass.MALFORMED,
            "R2-AUTH-003",
        )

    def test_malformed_public_inputs_do_not_throw(self) -> None:
        malformed_shape = replace(
            self.shared_shape,
            organization="SharedGrindingCore",
        )
        malformed_profile = replace(
            self.shared_profile,
            origin_policy="InterpretationAndSourceSensitive",
        )
        calls = (
            lambda: derive_relation_shape(object(), object()),
            lambda: derive_validation_profile(object(), object(), object()),
            lambda: check_typed_disposition_map(object(), object(), object(), object()),
            lambda: compare_mapped_values(object(), object(), object(), object()),
            lambda: compare_full_observations(object(), object(), object(), object()),
            lambda: compare_origins(object(), object(), object(), object()),
            lambda: compare_strategies(object(), object(), object(), object()),
            lambda: derive_hybrid_factorization(object(), object(), object(), object()),
            lambda: derive_relation_run_evidence(object(), object(), object(), object()),
            lambda: check_hybrid_factorization(
                object(), object(), object(), object(), object()
            ),
            lambda: protocol_statement_occurrence(object()),
            lambda: derive_pointwise_bridge(object(), object()),
            lambda: check_pointwise_bridge(object(), object()),
            lambda: statement_correspondence(object(), object()),
            lambda: check_anchor_authority(object(), object()),
            lambda: check_anchor_authority(
                self.fixture,
                AnchorReadRequest("contract", "ReferenceValue"),
            ),
            lambda: project_sha256_216(object()),
            lambda: classify_projection(object()),
            lambda: projection_loss_applicability(object()),
            lambda: check_typed_disposition_map(
                malformed_shape,
                self.shared_profile,
                self.coupled_grinding_qualified,
                self.fs_qualified,
            ),
            lambda: check_typed_disposition_map(
                self.shared_shape,
                malformed_profile,
                self.coupled_grinding_qualified,
                self.fs_qualified,
            ),
        )
        for call in calls:
            with self.subTest(call=call):
                result = call()
                self.assertIsInstance(result, CheckResult)
                assert isinstance(result, CheckResult)
                self.assertIsNot(result.outcome, OutcomeClass.CHECKER_FAILURE)


if __name__ == "__main__":
    unittest.main()
