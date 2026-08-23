from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest
from unittest import mock


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = MODEL_ROOT.parents[1]
sys.path.insert(0, str(MODEL_ROOT))

import r2model.execution as execution_module  # noqa: E402
from r2model.execution import (  # noqa: E402
    ExecutionRecord,
    QualifiedExecution,
    TraceEvent,
    TraceKind,
    admit_request,
    coupled_fresh_tape,
    execute,
    qualification_worst_case,
    qualify_execution,
    requalify,
    validate_terminal_law,
    worst_case_usage,
)
from r2model.frigrind import (  # noqa: E402
    Actor,
    ApplicationContext,
    CanonicalCodec,
    CoinVector,
    CoreDerivationKind,
    DEFAULT_RESOURCE_PLAN,
    ExecutionRequest,
    FixedNoncePlan,
    FreshTapeOrigin,
    Interpretation,
    MAX_QUALIFICATION_CAPS,
    Mutation,
    NonceSearchPlan,
    Provenance,
    TerminalKind,
    ValueSort,
    _freeze,
    admit_scenario,
    base_scenario,
    build_evaluator_basis,
    fresh_fri_scenario,
    fresh_grinding_scenario,
    load_fixture,
    load_external_fresh,
    load_invocation,
    mutate,
)
from r2model.terms import (  # noqa: E402
    CheckResult,
    OutcomeClass,
    SEMANTIC_REGIME_ID,
    semantic_id,
    supports_semantic_regime,
)


class ExecutionV3Test(unittest.TestCase):
    """Executable closure tests for the repaired FRI-Grind witness."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = load_fixture(REPO_ROOT)
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
        cls.source_fixture_id = f"sha256:{cls.fixture.sha256}"
        cls.source_package_id = cls.invocation.identity

        cls.fs_request = ExecutionRequest(
            cls.fs_scenario,
            cls.invocation.input_bundle,
            cls.application_context,
            cls.basis.identity,
            DEFAULT_RESOURCE_PLAN,
            CoreDerivationKind.FIXTURE_GRINDING_CORE,
            cls.source_fixture_id,
            cls.source_package_id,
            nonce_search=cls.invocation.default_search,
        )
        cls.fs_record = cls._record(execute(cls.fs_request, cls.basis))
        cls.fs_qualified = cls._qualified(
            qualify_execution(cls.fs_request, cls.basis, cls.fs_record)
        )
        cls.fs_nonce = cls.fs_record.prover_value("nonce")

        external_tape, external_nonce = load_external_fresh(
            REPO_ROOT,
            cls.fresh_grinding.core,
        )
        cls.external_tape = external_tape
        cls.external_nonce = external_nonce
        cls.external_request = ExecutionRequest(
            cls.fresh_grinding,
            cls.invocation.input_bundle,
            cls.application_context,
            cls.basis.identity,
            DEFAULT_RESOURCE_PLAN,
            CoreDerivationKind.FIXTURE_GRINDING_CORE,
            cls.source_fixture_id,
            cls.source_package_id,
            fixed_nonce=external_nonce,
            coin_tape=external_tape,
        )
        cls.external_record = cls._record(execute(cls.external_request, cls.basis))
        cls.external_qualified = cls._qualified(
            qualify_execution(cls.external_request, cls.basis, cls.external_record)
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
            cls.source_fixture_id,
            cls.source_package_id,
            fixed_nonce=FixedNoncePlan(cls.fs_nonce),
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
        cls.fri_tape = fri_tape
        cls.coupled_fri_request = ExecutionRequest(
            cls.fresh_fri,
            cls.invocation.input_bundle,
            cls.application_context,
            cls.basis.identity,
            DEFAULT_RESOURCE_PLAN,
            CoreDerivationKind.DROP_GRINDING_PROJECTION,
            cls.source_fixture_id,
            cls.source_package_id,
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

        # The first successful FS nonce proves that the preceding half-open
        # interval contains no winner. This produces a real bounded abort.
        if cls.fs_nonce > 0:
            abort_plan = NonceSearchPlan(0, cls.fs_nonce)
            cls.abort_request = replace(cls.fs_request, nonce_search=abort_plan)
            cls.abort_record = cls._record(execute(cls.abort_request, cls.basis))
        else:
            # This branch is deterministic but normally unreachable for the
            # frozen fixture. Find one singleton interval that is not a winner.
            for candidate in range(1, 1025):
                request = replace(
                    cls.fs_request,
                    nonce_search=NonceSearchPlan(candidate, candidate + 1),
                )
                record = cls._record(execute(request, cls.basis))
                if record.disposition is TerminalKind.ABORT:
                    cls.abort_request = request
                    cls.abort_record = record
                    break
            else:
                raise AssertionError("could not construct a bounded FS abort")
        if cls.abort_record.disposition is not TerminalKind.ABORT:
            raise AssertionError("the search-exhaustion fixture did not abort")
        cls.abort_qualified = cls._qualified(
            qualify_execution(cls.abort_request, cls.basis, cls.abort_record)
        )

        # Search policy and resource ceilings are request metadata, not FS
        # transcript seed material. Both variants still contain the winner.
        cls.short_search_request = replace(
            cls.fs_request,
            nonce_search=NonceSearchPlan(0, cls.fs_nonce + 1),
        )
        cls.short_search_record = cls._record(
            execute(cls.short_search_request, cls.basis)
        )
        cls.resource_variant_request = replace(
            cls.fs_request,
            resources=replace(DEFAULT_RESOURCE_PLAN, max_trace_events=63),
        )
        cls.resource_variant_record = cls._record(
            execute(cls.resource_variant_request, cls.basis)
        )
        cls.context_variant_request = replace(
            cls.fs_request,
            application_context=ApplicationContext(
                "zkc.r2.frigrind",
                "different-session",
            ),
        )
        cls.context_variant_record = cls._record(
            execute(cls.context_variant_request, cls.basis)
        )

    @staticmethod
    def _record(value: ExecutionRecord | CheckResult) -> ExecutionRecord:
        if isinstance(value, CheckResult):
            raise AssertionError(value)
        if not isinstance(value, ExecutionRecord):
            raise AssertionError(f"expected ExecutionRecord, got {type(value)!r}")
        return value

    @staticmethod
    def _qualified(value: QualifiedExecution | CheckResult) -> QualifiedExecution:
        if isinstance(value, CheckResult):
            raise AssertionError(value)
        if not isinstance(value, QualifiedExecution):
            raise AssertionError(f"expected QualifiedExecution, got {type(value)!r}")
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

    def test_four_execution_forms_are_closed_and_source_residual(self) -> None:
        forms = (
            (self.fs_request, self.fs_record, Interpretation.FS),
            (self.external_request, self.external_record, Interpretation.FRESH),
            (
                self.coupled_grinding_request,
                self.coupled_grinding_record,
                Interpretation.FRESH,
            ),
            (self.coupled_fri_request, self.coupled_fri_record, Interpretation.FRESH),
        )
        for request, record, interpretation in forms:
            with self.subTest(scenario=request.scenario.identity):
                self.assertIs(record.interpretation, interpretation)
                self.assertIs(record.disposition, TerminalKind.SOURCE_RESIDUAL)
                self.assertEqual(
                    tuple(event.occurrence for event in record.events),
                    request.scenario.core.schedule,
                )
                self.assert_result(
                    validate_terminal_law(request, record),
                    OutcomeClass.AFFIRMATIVE,
                )
        self.assertEqual(
            self.fs_scenario.core.identity,
            self.fresh_grinding.core.identity,
        )
        self.assertNotEqual(self.fs_scenario.identity, self.fresh_grinding.identity)
        self.assertNotEqual(
            self.fresh_grinding.construction.identity,
            self.fresh_fri.construction.identity,
        )
        self.assertIs(
            self.external_tape.origin,
            FreshTapeOrigin.EXTERNAL_FIXTURE,
        )
        self.assertIs(
            self.grinding_tape.origin,
            FreshTapeOrigin.DERIVED_EXECUTION,
        )

    def test_qualification_is_exact_and_dependency_usage_is_aggregated(self) -> None:
        for qualified in (
            self.fs_qualified,
            self.external_qualified,
            self.coupled_grinding_qualified,
            self.coupled_fri_qualified,
            self.abort_qualified,
        ):
            with self.subTest(qualified=qualified.identity):
                replayed = requalify(qualified)
                self.assertIsInstance(replayed, QualifiedExecution)
                assert isinstance(replayed, QualifiedExecution)
                self.assertEqual(replayed.identity, qualified.identity)

        usage = self.coupled_grinding_qualified.usage
        self.assertIsNotNone(usage)
        assert usage is not None
        self.assertEqual(usage.dependency_executions, 1)
        self.assertEqual(
            usage.nonce_candidates,
            self.coupled_grinding_record.usage.nonce_candidates
            + self.fs_qualified.usage.nonce_candidates,
        )
        self.assertEqual(
            usage.hash_queries,
            self.coupled_grinding_record.usage.hash_queries
            + self.fs_qualified.usage.hash_queries,
        )
        self.assertEqual(
            self.coupled_grinding_qualified.dependencies,
            (self.fs_qualified,),
        )

        changed_events = list(self.fs_record.events)
        changed_events[0] = replace(changed_events[0], value=changed_events[0].value + 1)
        forged_record = replace(self.fs_record, events=tuple(changed_events))
        self.assert_result(
            qualify_execution(self.fs_request, self.basis, forged_record),
            OutcomeClass.MISMATCH,
            "R2-QUAL-003",
        )
        forged_usage = replace(
            self.coupled_grinding_qualified.usage,
            hash_queries=self.coupled_grinding_qualified.usage.hash_queries + 1,
        )
        forged_qualification = replace(
            self.coupled_grinding_qualified,
            usage=forged_usage,
        )
        self.assert_result(
            requalify(forged_qualification),
            OutcomeClass.MISMATCH,
            "R2-QUAL-005",
        )

    def test_external_fresh_tape_is_exactly_reconstructed(self) -> None:
        vectors = list(self.external_tape.vectors)
        first = vectors[0]
        cardinality = self.external_request.scenario.core.action(
            first.challenge_occurrence
        ).cardinality
        assert cardinality is not None
        vectors[0] = replace(
            first,
            values=((first.values[0] + 1) % cardinality,),
        )
        forged_values = replace(self.external_tape, vectors=tuple(vectors))
        forged_dependency = replace(
            self.external_tape,
            dependency_execution_id=self.fs_record.identity,
        )
        forged_source = replace(
            self.external_tape,
            source_id=semantic_id("hostile.external-tape", {}),
        )
        for tape in (forged_values, forged_dependency, forged_source):
            with self.subTest(tape=tape.identity):
                request = replace(self.external_request, coin_tape=tape)
                result = admit_request(request, self.basis)
                self.assertIsInstance(result, CheckResult)
                self.assertIn(
                    result.outcome,
                    {OutcomeClass.MISMATCH, OutcomeClass.MALFORMED},
                )
        self.assert_result(
            admit_request(
                self.external_request,
                self.basis,
                (self.fs_qualified,),
            ),
            OutcomeClass.MISMATCH,
            "R2-COUPLE-003",
        )

    def test_derived_fresh_tape_requires_the_exact_qualified_source(self) -> None:
        self.assert_result(
            admit_request(self.coupled_grinding_request, self.basis),
            OutcomeClass.MISSING_DEPENDENCY,
            "R2-COUPLE-005",
        )

        fake_id = semantic_id("hostile.execution", {})
        forged_binding = replace(
            self.grinding_tape,
            source_id=fake_id,
            dependency_execution_id=fake_id,
        )
        forged_request = replace(
            self.coupled_grinding_request,
            coin_tape=forged_binding,
        )
        self.assert_result(
            admit_request(forged_request, self.basis, (self.fs_qualified,)),
            OutcomeClass.MISMATCH,
            "R2-COUPLE-008",
        )

        vectors = list(self.grinding_tape.vectors)
        pow_index = next(
            index
            for index, vector in enumerate(vectors)
            if vector.challenge_occurrence == "challenge:pow"
        )
        vectors[pow_index] = CoinVector("challenge:pow", (1,))
        forged_projection = replace(self.grinding_tape, vectors=tuple(vectors))
        forged_request = replace(
            self.coupled_grinding_request,
            coin_tape=forged_projection,
        )
        self.assert_result(
            admit_request(forged_request, self.basis, (self.fs_qualified,)),
            OutcomeClass.MISMATCH,
            "R2-COUPLE-010",
        )

        changed_source_record = replace(
            self.fs_record,
            events=self.fs_record.events[:-1],
        )
        changed_source = replace(self.fs_qualified, record=changed_source_record)
        result = admit_request(
            self.coupled_grinding_request,
            self.basis,
            (changed_source,),
        )
        self.assertIsInstance(result, CheckResult)
        self.assertIn(
            result.outcome,
            {OutcomeClass.MISMATCH, OutcomeClass.MISSING_DEPENDENCY},
        )

    def test_source_package_and_core_are_grounded_independently_of_admission(self) -> None:
        wrong_source = replace(
            self.fs_request,
            source_package_id=semantic_id("hostile.source-package", {}),
        )
        self.assert_result(
            admit_request(wrong_source, self.basis),
            OutcomeClass.MISMATCH,
            "R2-REQ-019",
        )
        wrong_derivation = replace(
            self.fs_request,
            core_derivation=CoreDerivationKind.DROP_GRINDING_PROJECTION,
        )
        self.assert_result(
            admit_request(wrong_derivation, self.basis),
            OutcomeClass.MISMATCH,
            "R2-REQ-019",
        )

        post_grind = mutate(self.fs_scenario, Mutation.POST_GRIND_ABSORB)
        self.assert_result(admit_scenario(post_grind), OutcomeClass.AFFIRMATIVE)
        post_basis = build_evaluator_basis(
            REPO_ROOT,
            {
                self.fs_scenario.construction.identity,
                self.fresh_grinding.construction.identity,
                post_grind.construction.identity,
            },
        )
        post_request = replace(
            self.fs_request,
            scenario=post_grind,
            evaluator_basis_id=post_basis.identity,
        )
        self.assert_result(
            admit_request(post_request, post_basis),
            OutcomeClass.MISMATCH,
            "R2-REQ-019",
        )

    def test_request_metadata_is_not_transcript_seed_but_context_is(self) -> None:
        baseline = self.fs_record.challenge_values()
        for request, record in (
            (self.short_search_request, self.short_search_record),
            (self.resource_variant_request, self.resource_variant_record),
        ):
            with self.subTest(request=request.identity):
                self.assertNotEqual(request.identity, self.fs_request.identity)
                self.assertEqual(record.challenge_values(), baseline)
                self.assertEqual(record.prover_value("nonce"), self.fs_nonce)

        self.assertNotEqual(
            self.context_variant_request.application_context.identity,
            self.fs_request.application_context.identity,
        )
        self.assertNotEqual(
            self.context_variant_record.challenge_values(),
            baseline,
        )

    def test_statement_and_field_codecs_are_total_at_the_profile_maximum(self) -> None:
        construction = self.fs_scenario.construction
        statement_codec = construction.codec_for("statement:f_root")
        g1_codec = construction.codec_for("message:g1")
        self.assertEqual(statement_codec.width, 16)
        self.assertEqual(g1_codec.width, 16)
        self.assertEqual(len(statement_codec.encode(self.fs_scenario.field - 1)), 16)

        maximum = CanonicalCodec(
            "r2.rs.be16.maximum-test",
            ValueSort.RS,
            16,
            1 << 128,
        )
        self.assertTrue(maximum.is_total)
        self.assertEqual(maximum.encode((1 << 128) - 1), b"\xff" * 16)
        with self.assertRaises(ValueError):
            maximum.encode(1 << 128)
        with self.assertRaises(ValueError):
            maximum.encode(True)

    def test_core_mutations_and_strategy_coverage_fail_at_owned_boundaries(self) -> None:
        expected = {
            Mutation.OMIT_STATEMENT: (OutcomeClass.MISMATCH, "R2-FS-001"),
            Mutation.DELAY_STATEMENT: (OutcomeClass.MISMATCH, "R2-FS-002"),
            Mutation.DUPLICATE_STATEMENT: (OutcomeClass.MISMATCH, "R2-FS-003"),
            Mutation.WRONG_STATEMENT_CODEC: (OutcomeClass.MALFORMED, "R2-FRM-002"),
            Mutation.G1_WIRE_ONLY: (OutcomeClass.MISMATCH, "R2-FS-005"),
            Mutation.NONCE_WIRE_ONLY: (OutcomeClass.MISMATCH, "R2-FS-005"),
            Mutation.NAMESPACE_COLLISION: (OutcomeClass.MISMATCH, "R2-NS-001"),
            Mutation.VERIFIER_PRIVATE_DEPENDENCY: (
                OutcomeClass.MISMATCH,
                "R2-PC-001",
            ),
            Mutation.G1_FUTURE_POW: (OutcomeClass.MISMATCH, "R2-CAUSAL-001"),
            Mutation.G1_FUTURE_QUERY: (OutcomeClass.MISMATCH, "R2-CAUSAL-001"),
            Mutation.ROUTE_ORDER: (OutcomeClass.MISMATCH, "R2-ROUTE-001"),
        }
        for mutation, (outcome, code) in expected.items():
            with self.subTest(mutation=mutation.value):
                self.assert_result(
                    admit_scenario(mutate(self.fs_scenario, mutation)),
                    outcome,
                    code,
                )

        post_grind = mutate(self.fs_scenario, Mutation.POST_GRIND_ABSORB)
        self.assert_result(admit_scenario(post_grind), OutcomeClass.AFFIRMATIVE)
        self.assertEqual(
            tuple(strategy.output_occurrence for strategy in post_grind.strategies),
            tuple(
                action.occurrence
                for action in post_grind.core.actions
                if action.kind.value == "Message"
            ),
        )
        missing_strategy = replace(
            post_grind,
            strategies=post_grind.strategies[:-1],
        )
        self.assert_result(
            admit_scenario(missing_strategy),
            OutcomeClass.MISMATCH,
            "R2-CAUSAL-005",
        )

    def test_abort_reject_and_residual_terminal_laws_are_exact(self) -> None:
        self.assert_result(
            validate_terminal_law(self.abort_request, self.abort_record),
            OutcomeClass.AFFIRMATIVE,
            "R2-TERM-102",
        )
        self.assert_result(
            validate_terminal_law(
                self.abort_request,
                replace(self.abort_record, events=self.abort_record.events[:-1]),
            ),
            OutcomeClass.MISMATCH,
        )
        abort_continued = replace(
            self.abort_record,
            events=self.abort_record.events + (self.fs_record.events[3],),
        )
        self.assert_result(
            validate_terminal_law(self.abort_request, abort_continued),
            OutcomeClass.MISMATCH,
        )

        self.assert_result(
            validate_terminal_law(self.external_request, self.external_record),
            OutcomeClass.AFFIRMATIVE,
            "R2-TERM-100",
        )
        missing_residual = replace(
            self.external_record,
            events=self.external_record.events[:-1],
        )
        self.assert_result(
            validate_terminal_law(self.external_request, missing_residual),
            OutcomeClass.MISMATCH,
            "R2-TERM-003",
        )
        events = list(self.external_record.events)
        pow_check_index = self.external_request.scenario.core.schedule.index(
            "check:pow_zero"
        )
        events[pow_check_index] = replace(events[pow_check_index], value=False)
        continued_after_reject = replace(self.external_record, events=tuple(events))
        self.assert_result(
            validate_terminal_law(self.external_request, continued_after_reject),
            OutcomeClass.MISMATCH,
            "R2-TERM-011",
        )

        terminal = TraceEvent(
            "terminal:pow_zero",
            TraceKind.TERMINAL,
            Actor.VERIFIER,
            TerminalKind.REJECT,
            Provenance.DETERMINISTIC_VERIFIER,
        )
        reject_record = replace(
            self.external_record,
            events=tuple(events[: pow_check_index + 1]) + (terminal,),
            disposition=TerminalKind.REJECT,
        )
        self.assert_result(
            validate_terminal_law(self.external_request, reject_record),
            OutcomeClass.AFFIRMATIVE,
            "R2-TERM-101",
        )
        for attacked in (
            replace(reject_record, events=reject_record.events[:-1]),
            replace(reject_record, events=reject_record.events + (terminal,)),
            replace(
                reject_record,
                events=reject_record.events[:-1]
                + (replace(terminal, actor=Actor.PROVER),),
            ),
            replace(
                reject_record,
                events=reject_record.events + (self.external_record.events[pow_check_index + 1],),
            ),
        ):
            with self.subTest(events=len(attacked.events)):
                self.assert_result(
                    validate_terminal_law(self.external_request, attacked),
                    OutcomeClass.MISMATCH,
                )
        self.assert_result(
            qualify_execution(
                self.external_request,
                self.basis,
                reject_record,
            ),
            OutcomeClass.MISMATCH,
            "R2-QUAL-003",
        )

    def test_aggregate_resource_caps_are_checked_before_execution(self) -> None:
        tiny = replace(DEFAULT_RESOURCE_PLAN, max_nonce_candidates=1)
        over_budget = replace(self.fs_request, resources=tiny)
        worst = worst_case_usage(over_budget)
        self.assertIsNotNone(worst)
        with mock.patch.object(
            execution_module,
            "_Transcript",
            side_effect=AssertionError("execution must not begin"),
        ) as transcript:
            result = execute(over_budget, self.basis)
        transcript.assert_not_called()
        self.assert_result(
            result,
            OutcomeClass.RESOURCE_EXCEEDED,
            "R2-REQ-006",
        )

        oversized_search = replace(
            self.fs_request,
            nonce_search=NonceSearchPlan(0, 1_000_001),
        )
        self.assert_result(
            admit_request(oversized_search, self.basis),
            OutcomeClass.RESOURCE_EXCEEDED,
            "R2-REQ-006",
        )

    def test_qualification_caps_precede_reexecution(self) -> None:
        low_caps = replace(MAX_QUALIFICATION_CAPS, max_total_trace_events=1)
        low_basis = build_evaluator_basis(
            REPO_ROOT,
            {
                self.fs_scenario.construction.identity,
                self.fresh_grinding.construction.identity,
            },
            qualification_caps=low_caps,
        )
        low_request = replace(
            self.external_request,
            evaluator_basis_id=low_basis.identity,
        )
        low_record = self._record(execute(low_request, low_basis))
        self.assert_result(
            qualification_worst_case(low_request, low_basis),
            OutcomeClass.RESOURCE_EXCEEDED,
            "R2-QUAL-009",
        )
        with mock.patch.object(
            execution_module,
            "execute",
            side_effect=AssertionError("qualification replay must not begin"),
        ) as replay:
            result = qualify_execution(low_request, low_basis, low_record)
        replay.assert_not_called()
        self.assert_result(
            result,
            OutcomeClass.RESOURCE_EXCEEDED,
            "R2-QUAL-009",
        )

    def test_malformed_public_inputs_never_escape_as_checker_exceptions(self) -> None:
        raw_interpretation = replace(
            self.fs_scenario,
            interpretation="FiatShamir",
        )
        bool_statement = replace(
            self.fs_request,
            inputs=replace(self.fs_request.inputs, statement_value=True),
        )
        bool_search = replace(
            self.fs_request,
            nonce_search=NonceSearchPlan(True, 2),
        )
        bool_resource = replace(
            self.fs_request,
            resources=replace(DEFAULT_RESOURCE_PLAN, max_nonce_candidates=True),
        )
        long_context = replace(
            self.fs_request,
            application_context=ApplicationContext("x" * 257, "session"),
        )
        raw_tape = replace(self.external_tape, origin="ExternalFixture")
        raw_tape_request = replace(self.external_request, coin_tape=raw_tape)
        raw_derivation = replace(
            self.fs_request,
            core_derivation="FixtureGrindingCore",
        )

        malformed_requests = (
            bool_statement,
            bool_search,
            bool_resource,
            long_context,
            raw_tape_request,
            raw_derivation,
        )
        for request in malformed_requests:
            with self.subTest(request=type(request).__name__):
                result = execute(request, self.basis)
                self.assertIsInstance(result, CheckResult)
                assert isinstance(result, CheckResult)
                self.assertIsNot(result.outcome, OutcomeClass.CHECKER_FAILURE)
        self.assert_result(
            admit_scenario(raw_interpretation),
            OutcomeClass.MALFORMED,
            "R2-ADM-003",
        )

        public_calls = (
            lambda: admit_scenario(object()),
            lambda: worst_case_usage(object()),
            lambda: admit_request(object(), self.basis),
            lambda: execute(object(), self.basis),
            lambda: validate_terminal_law(object(), self.fs_record),
            lambda: validate_terminal_law(self.fs_request, object()),
            lambda: qualify_execution(self.fs_request, self.basis, object()),
            lambda: requalify(object()),
            lambda: coupled_fresh_tape(object(), self.fs_scenario.core),
            lambda: qualification_worst_case(self.fs_request, object()),
        )
        for call in public_calls:
            with self.subTest(call=call):
                result = call()
                self.assertIsInstance(result, CheckResult)
                assert isinstance(result, CheckResult)
                self.assertIsNot(result.outcome, OutcomeClass.CHECKER_FAILURE)

    def test_fixture_freeze_and_identity_terms_distinguish_maps_and_lists(self) -> None:
        self.assertNotEqual(_freeze({"value": []}), _freeze({"value": {}}))
        self.assertNotEqual(
            semantic_id("r2.freeze-test", {"value": []}),
            semantic_id("r2.freeze-test", {"value": {}}),
        )
        first_payload = self.fixture.payload
        first_payload["anchors"]["statement"] = "hostile"
        self.assertNotEqual(
            first_payload["anchors"]["statement"],
            self.fixture.payload["anchors"]["statement"],
        )
        self.assertTrue(supports_semantic_regime(SEMANTIC_REGIME_ID))
        self.assertFalse(
            supports_semantic_regime(semantic_id("hostile.regime", {}))
        )


if __name__ == "__main__":
    unittest.main()
