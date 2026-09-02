from __future__ import annotations

from dataclasses import replace
import inspect
import json
from pathlib import Path
import unittest

import independent_oracle
import independent_target
import model


HERE = Path(__file__).resolve().parents[1]


def _tuple_values(value):
    if isinstance(value, list):
        return tuple(_tuple_values(item) for item in value)
    if isinstance(value, dict):
        return {key: _tuple_values(item) for key, item in value.items()}
    return value


def _fixture():
    raw = independent_oracle.load_fixture()
    inputs = _tuple_values(raw["inputs"])
    oracles = {
        name: {index: value for index, value in entries}
        for name, entries in raw["oracles"].items()
    }
    return inputs, model.freeze_oracles(oracles)


class ErrorAssertions(unittest.TestCase):
    def assertPlanError(self, outcome, operation):
        with self.assertRaises(model.PlanError) as caught:
            operation()
        self.assertEqual(caught.exception.outcome, outcome)
        self.assertTrue(caught.exception.code.startswith("VDQP-"))
        return caught.exception


class ProgramFormationTest(ErrorAssertions):
    def setUp(self):
        self.programs = model.representative_programs()
        self.plan = model.representative_plan()

    def test_representative_catalog_and_plan_form(self):
        self.assertEqual(len(self.programs), 5)
        self.assertEqual(len(self.plan.sites), 5)
        self.assertEqual(
            model.program_id(self.programs["stir-folded-word"]),
            "4bcf1c25a3801603de66e215baedac620e28d23275bf403b76773c2c1f68efcf",
        )
        self.assertEqual(
            model.plan_id(self.plan, self.programs),
            "c301e7600d2d35affe6a28045631f90014063188dd862c7eaa7c6ad6ce6b47a5",
        )

    def test_exact_program_bounds_are_derived_not_advisory(self):
        folded = self.programs["stir-folded-word"]
        changed = dict(self.programs)
        changed[folded.name] = replace(folded, maximum_leaf_reads=3)
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_programs(changed),
        )

    def test_program_cycle_refuses(self):
        folded = self.programs["stir-folded-word"]
        case = folded.cases[0]
        call = next(step for step in case.steps if isinstance(step, model.CallStep))
        cyclic_call = replace(
            call,
            program=folded.name,
            arguments=(
                ("answers", "answers"),
                ("challenge", "challenge"),
                ("points", "points"),
            ),
            oracle_bindings=(("fill", "fill"), ("source", "source")),
        )
        steps = tuple(cyclic_call if step is call else step for step in case.steps)
        changed = dict(self.programs)
        changed[folded.name] = replace(folded, cases=(replace(case, steps=steps),))
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_programs(changed),
        )

    def test_answer_dependent_source_index_refuses(self):
        quotient = self.programs["stir-quotient-word"]
        outside = next(case for case in quotient.cases if case.tag == "outside")
        adaptive = model.ReadStep("adaptive-read", "source", "source-value")
        changed_case = replace(
            outside,
            steps=outside.steps + (adaptive,),
            result="adaptive-read",
        )
        cases = tuple(changed_case if case is outside else case for case in quotient.cases)
        changed = dict(self.programs)
        changed[quotient.name] = replace(quotient, cases=cases, maximum_leaf_reads=2)
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_programs(changed),
        )

    def test_incomplete_route_partition_refuses(self):
        quotient = self.programs["multipoint-quotient-word"]
        changed = dict(self.programs)
        changed[quotient.name] = replace(quotient, cases=(quotient.cases[0],))
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_programs(changed),
        )

    def test_verifier_only_source_cannot_be_declassified(self):
        circle = self.programs["circle-batched-word"]
        ports = (replace(circle.oracle_ports[0], visibility=model.Visibility.VERIFIER_ONLY),) + circle.oracle_ports[1:]
        changed = dict(self.programs)
        changed[circle.name] = replace(circle, oracle_ports=ports)
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_programs(changed),
        )

    def test_transitive_verifier_only_source_cannot_be_declassified(self):
        quotient = self.programs["stir-quotient-word"]
        folded = self.programs["stir-folded-word"]
        changed = dict(self.programs)
        changed[quotient.name] = replace(
            quotient,
            oracle_ports=tuple(
                replace(port, visibility=model.Visibility.VERIFIER_ONLY)
                for port in quotient.oracle_ports
            ),
            output_visibility=model.Visibility.VERIFIER_ONLY,
        )
        changed[folded.name] = replace(
            folded,
            oracle_ports=tuple(
                replace(port, visibility=model.Visibility.VERIFIER_ONLY)
                for port in folded.oracle_ports
            ),
        )
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_programs(changed),
        )

    def test_prime_field_profile_refuses_composite_modulus(self):
        circle = self.programs["circle-batched-word"]
        changed = dict(self.programs)
        changed[circle.name] = replace(circle, modulus=15)
        error = self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_programs(changed),
        )
        self.assertEqual(error.boundary, "formation:algebra")

    def test_componentwise_program_bounds_are_not_lexicographic(self):
        leaf = model.DerivedWordProgram(
            name="leaf",
            modulus=17,
            algebra_profile=model.AlgebraProfile.PRIME_FIELD,
            arguments=(),
            oracle_ports=(model.OraclePort("source"),),
            route_algorithm="always",
            route_inputs=(),
            cases=(
                model.ProgramCase(
                    "only",
                    (model.ReadStep("read", "source", "index"),),
                    result="read",
                ),
            ),
            output_visibility=model.Visibility.PUBLIC,
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=1,
        )
        mixed = model.DerivedWordProgram(
            name="mixed",
            modulus=17,
            algebra_profile=model.AlgebraProfile.PRIME_FIELD,
            arguments=(),
            oracle_ports=(model.OraclePort("source"),),
            route_algorithm="zero-vs-nonzero",
            route_inputs=("index",),
            cases=(
                model.ProgramCase(
                    "nonzero",
                    (
                        model.CallStep(
                            "child",
                            "leaf",
                            "index",
                            (),
                            (("source", "source"),),
                        ),
                    ),
                    result="child",
                ),
                model.ProgramCase(
                    "zero",
                    tuple(
                        model.ReadStep(f"read-{index}", "source", "index")
                        for index in range(4)
                    ),
                    result="read-3",
                ),
            ),
            output_visibility=model.Visibility.PUBLIC,
            output_is_boolean=False,
            maximum_elaboration_depth=2,
            maximum_leaf_reads=4,
        )
        catalog = {"leaf": leaf, "mixed": mixed}
        self.assertEqual(model._program_metrics("mixed", catalog), (2, 4))
        model.validate_programs(catalog)

    def test_plan_requires_total_argument_and_oracle_bindings(self):
        site = self.plan.sites[0]
        broken = replace(site, oracle_bindings=site.oracle_bindings[:-1])
        sites = (broken,) + self.plan.sites[1:]
        self.assertPlanError(
            model.OutcomeClass.KIND_MISMATCH,
            lambda: model.validate_plan(replace(self.plan, sites=sites), self.programs),
        )

    def test_semantic_mutation_rotates_program_and_plan_identity(self):
        circle = self.programs["circle-batched-word"]
        changed = dict(self.programs)
        changed[circle.name] = replace(
            circle, output_visibility=model.Visibility.VERIFIER_ONLY
        )
        changed = model.validate_programs(changed)
        self.assertNotEqual(
            model.program_id(circle), model.program_id(changed[circle.name])
        )
        self.assertNotEqual(
            model.plan_id(self.plan, self.programs),
            model.plan_id(self.plan, changed),
        )


class StaticElaborationTest(ErrorAssertions):
    def setUp(self):
        self.programs = model.representative_programs()
        self.plan = model.representative_plan()
        events, _ = model.derive_static_template(self.plan, self.programs)
        self.target_core = model.admit_flat_core(events)
        self.elaboration = model.elaborate(
            self.plan, self.programs, self.target_core
        )

    def test_complete_elaboration_checks(self):
        checked = model.check_elaboration(
            self.plan, self.programs, self.target_core, self.elaboration
        )
        self.assertEqual(checked.event_count, 62)
        self.assertEqual(checked.plan_id, self.elaboration.plan_id)

    def test_static_elaboration_limit_is_external_and_fail_closed(self):
        error = self.assertPlanError(
            model.OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            lambda: model.derive_static_template(
                self.plan,
                self.programs,
                maximum_static_events=61,
            ),
        )
        self.assertEqual(error.boundary, "elaboration:budget")

    def test_flattened_events_have_no_derived_publication_or_runtime_emission(self):
        kinds = {event.kind for event in self.elaboration.events}
        self.assertFalse(
            kinds
            & {"PublishDerivedOracle", "AbsorbDerivedDeclaration", "RuntimeEmit"}
        )
        self.assertEqual(
            kinds,
            {
                "AnswerOracle",
                "BindNestedResult",
                "DerivedValue",
                "QueryOracle",
                "ReachSemanticTerminal",
                "ReturnDerivedValue",
                "Route",
            },
        )

        invented = model.StaticEvent(
            "PublishDerivedOracle",
            ("invented",),
            (),
            (),
        )
        candidate = replace(
            self.elaboration,
            events=self.elaboration.events + (invented,),
        )
        error = self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.check_elaboration(
                self.plan, self.programs, self.target_core, candidate
            ),
        )
        self.assertEqual(error.boundary, "checking:authority")

    def test_logical_map_retains_every_static_branch_and_leaf(self):
        mapping = dict(self.elaboration.logical_to_source_events)
        self.assertEqual(len(mapping["circle-batch"]), 3)
        self.assertEqual(len(mapping["deep-first-quotient"]), 1)
        self.assertEqual(len(mapping["deep-second-quotient"]), 1)
        self.assertEqual(len(mapping["stir-fold"]), 4)
        self.assertEqual(len(mapping["whir-grouped-fold"]), 4)
        for ordinals in mapping.values():
            self.assertTrue(
                all(self.elaboration.events[ordinal].kind == "QueryOracle" for ordinal in ordinals)
            )

    def test_missing_or_reordered_event_refuses(self):
        missing = replace(self.elaboration, events=self.elaboration.events[:-1])
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.check_elaboration(
                self.plan, self.programs, self.target_core, missing
            ),
        )
        events = list(self.elaboration.events)
        events[1], events[2] = events[2], events[1]
        reordered = replace(self.elaboration, events=tuple(events))
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.check_elaboration(
                self.plan, self.programs, self.target_core, reordered
            ),
        )

    def test_multiplicity_loss_in_map_refuses(self):
        mapping = list(self.elaboration.logical_to_source_events)
        site, ordinals = mapping[0]
        mapping[0] = (site, ordinals[:-1])
        candidate = replace(
            self.elaboration, logical_to_source_events=tuple(mapping)
        )
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.check_elaboration(
                self.plan, self.programs, self.target_core, candidate
            ),
        )

    def test_wrong_plan_or_target_identity_is_not_reinterpreted(self):
        wrong_plan = replace(self.elaboration, plan_id="00" * 32)
        self.assertPlanError(
            model.OutcomeClass.KIND_MISMATCH,
            lambda: model.check_elaboration(
                self.plan, self.programs, self.target_core, wrong_plan
            ),
        )
        wrong_target = replace(self.elaboration, target_core_id="11" * 32)
        self.assertPlanError(
            model.OutcomeClass.KIND_MISMATCH,
            lambda: model.check_elaboration(
                self.plan, self.programs, self.target_core, wrong_target
            ),
        )


class RuntimeWitnessTest(ErrorAssertions):
    def setUp(self):
        self.programs = model.representative_programs()
        self.plan = model.representative_plan()
        self.inputs, self.oracles = _fixture()
        self.independent = independent_oracle.evaluate()

    def _execute(self, site, *, inputs=None, oracles=None, work_limit=10_000):
        return model.execute_site(
            plan=self.plan,
            programs=self.programs,
            site_name=site,
            inputs=self.inputs if inputs is None else inputs,
            oracles=self.oracles if oracles is None else oracles,
            work_limit=work_limit,
        )

    def test_all_four_family_shapes_match_independent_oracle(self):
        for site, expected in self.independent["values"].items():
            with self.subTest(site=site):
                result = self._execute(site)
                self.assertIsNone(result.terminal)
                self.assertEqual(result.value, expected)

    def test_exact_ordered_leaf_queries_match_independent_oracle(self):
        for site, expected in self.independent["queries"].items():
            with self.subTest(site=site):
                result = self._execute(site)
                actual = [[query.source_oracle, query.index] for query in result.queries]
                self.assertEqual(actual, expected)

    def test_stir_nested_fold_exercises_fill_and_source_routes(self):
        result = self._execute("stir-fold")
        self.assertEqual(
            [(query.source_oracle, query.index) for query in result.queries],
            [("stir-fill", 2), ("stir-source", 15)],
        )

    def test_deep_collision_reaches_explicit_terminal_without_source_read(self):
        inputs = dict(self.inputs)
        inputs["deep-index"] = 1
        result = self._execute("deep-first-quotient", inputs=inputs)
        self.assertEqual(result.terminal, "UndefinedQuotient")
        self.assertIsNone(result.value)
        self.assertEqual(result.queries, ())

    def test_missing_oracle_and_absent_entry_remain_distinct(self):
        missing = model.freeze_oracles(
            {name: values for name, values in self.oracles.items() if name != "deep-first"}
        )
        self.assertPlanError(
            model.OutcomeClass.MISSING_DEPENDENCY,
            lambda: self._execute("deep-first-quotient", oracles=missing),
        )
        absent_tables = {name: dict(values) for name, values in self.oracles.items()}
        del absent_tables["deep-first"][self.inputs["deep-index"]]
        absent = model.freeze_oracles(absent_tables)
        self.assertPlanError(
            model.OutcomeClass.CANNOT_ANSWER,
            lambda: self._execute("deep-first-quotient", oracles=absent),
        )

    def test_evaluator_exhaustion_is_limit_not_protocol_rejection(self):
        error = self.assertPlanError(
            model.OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
            lambda: self._execute("whir-grouped-fold", work_limit=2),
        )
        self.assertEqual(error.boundary, "execution:budget")

    def test_partial_fold_is_routed_to_an_explicit_terminal(self):
        inputs = dict(self.inputs)
        inputs["stir-index"] = 0
        result = self._execute("stir-fold", inputs=inputs)
        self.assertEqual(result.terminal, "UndefinedFold")
        self.assertIsNone(result.value)
        self.assertEqual(result.queries, ())

    def test_field_zero_representation_is_routed_before_inversion(self):
        inputs = dict(self.inputs)
        inputs["stir-index"] = 17
        result = self._execute("stir-fold", inputs=inputs)
        self.assertEqual(result.terminal, "UndefinedFold")
        self.assertEqual(result.queries, ())

    def test_invalid_interpolation_shape_is_an_explicit_terminal(self):
        inputs = dict(self.inputs)
        inputs["deep-answers-first"] = (inputs["deep-answers-first"][0],)
        result = self._execute("deep-first-quotient", inputs=inputs)
        self.assertEqual(result.terminal, "InvalidQuotientDomain")
        self.assertEqual(result.queries, ())

    def test_repeated_source_reads_are_not_deduplicated(self):
        site = self.plan.sites[0]
        repeated = replace(
            site,
            oracle_bindings=(
                ("first", "circle-first"),
                ("second", "circle-first"),
                ("third", "circle-third"),
            ),
        )
        plan = replace(self.plan, sites=(repeated,) + self.plan.sites[1:])
        result = model.execute_site(
            plan=plan,
            programs=self.programs,
            site_name="circle-batch",
            inputs=self.inputs,
            oracles=self.oracles,
        )
        self.assertEqual(
            [(query.source_oracle, query.index) for query in result.queries[:2]],
            [("circle-first", 6), ("circle-first", 6)],
        )

    def test_runtime_input_changes_value_but_not_plan_identity(self):
        original_id = model.plan_id(self.plan, self.programs)
        inputs = dict(self.inputs)
        inputs["circle-coefficient"] = 4
        changed = self._execute("circle-batch", inputs=inputs)
        self.assertNotEqual(changed.value, self.independent["values"]["circle-batch"])
        self.assertEqual(original_id, model.plan_id(self.plan, self.programs))

    def test_oracle_snapshots_are_immutable(self):
        with self.assertRaises(TypeError):
            self.oracles["deep-first"][5] = 0
        with self.assertRaises(TypeError):
            self.oracles["new"] = {}


class ActivationAndPriorResultClosureTest(ErrorAssertions):
    def setUp(self):
        self.programs = model.activation_and_prior_result_programs()
        self.plan = model.activation_and_prior_result_plan()
        plain = independent_target.activation_and_prior_result_events()
        self.events = tuple(model.StaticEvent(**item) for item in plain)
        self.target_core = model.admit_flat_core(self.events)

    def test_independent_target_is_the_complete_expected_core(self):
        expected, mapping = model.derive_static_template(self.plan, self.programs)
        self.assertEqual(self.events, expected)
        elaboration = model.elaborate(
            self.plan, self.programs, self.target_core
        )
        checked = model.check_elaboration(
            self.plan,
            self.programs,
            self.target_core,
            elaboration,
        )
        self.assertEqual(checked.event_count, 9)
        self.assertEqual([len(items) for _, items in mapping], [1, 1])

    def test_prior_answer_is_allowed_only_in_value_flow(self):
        results = model.execute_plan(
            plan=self.plan,
            programs=self.programs,
            inputs={"active": True, "first-index": 2, "second-index": 3},
            oracles=model.freeze_oracles(
                {"first-source": {2: 5}, "second-source": {3: 7}}
            ),
        )
        self.assertEqual(results["first-read"].value, 5)
        self.assertEqual(results["second-combination"].value, 12)

        second = self.plan.sites[1]
        adaptive_index = replace(
            second, requested_index=model.prior_logical_result("first-read")
        )
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_plan(
                replace(self.plan, sites=(self.plan.sites[0], adaptive_index)),
                self.programs,
            ),
        )

    def test_read_free_launderer_does_not_clear_answer_taint(self):
        launder = model.DerivedWordProgram(
            name="launder-word",
            modulus=17,
            algebra_profile=model.AlgebraProfile.PRIME_FIELD,
            arguments=("value",),
            oracle_ports=(),
            route_algorithm="always",
            route_inputs=(),
            cases=(
                model.ProgramCase(
                    "only",
                    (model.PureStep("copy", "identity", ("value",)),),
                    result="copy",
                ),
            ),
            output_visibility=model.Visibility.PUBLIC,
            output_is_boolean=False,
            maximum_elaboration_depth=1,
            maximum_leaf_reads=0,
        )
        programs = model.validate_programs({**self.programs, launder.name: launder})
        producer = self.plan.sites[0]
        laundering_site = model.PlanSite(
            "laundered-result",
            launder.name,
            model.LogicalActivation(),
            model.plan_input("second-index"),
            (("value", model.prior_logical_result("first-read")),),
            (),
        )
        adaptive_site = replace(
            producer,
            name="adaptive-read",
            requested_index=model.prior_logical_result("laundered-result"),
            oracle_bindings=(("source", "second-source"),),
        )
        adaptive_plan = replace(
            self.plan,
            name="answer-taint-laundering-regression",
            sites=(producer, laundering_site, adaptive_site),
        )
        error = self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_plan(adaptive_plan, programs),
        )
        self.assertEqual(error.code, "VDQP-FORM-031")

        boolean_programs = dict(programs)
        boolean_programs["read-word"] = replace(
            boolean_programs["read-word"], output_is_boolean=True
        )
        boolean_programs[launder.name] = replace(launder, output_is_boolean=True)
        boolean_programs = model.validate_programs(boolean_programs)
        activated_site = replace(
            adaptive_site,
            requested_index=model.plan_input("second-index"),
            activation=model.LogicalActivation(
                model.prior_logical_result("laundered-result")
            ),
        )
        activation_plan = replace(
            adaptive_plan,
            name="answer-taint-laundering-activation-regression",
            sites=(producer, laundering_site, activated_site),
        )
        error = self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_plan(activation_plan, boolean_programs),
        )
        self.assertEqual(error.code, "VDQP-FORM-053")

    def test_future_logical_result_is_refused_not_missing(self):
        future_first = replace(
            self.plan.sites[0],
            requested_index=model.prior_logical_result("second-combination"),
        )
        error = self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_plan(
                replace(
                    self.plan,
                    sites=(future_first, self.plan.sites[1]),
                ),
                self.programs,
            ),
        )
        self.assertEqual(error.boundary, "formation:plan-reference")

    def test_answer_tainted_activation_refuses(self):
        producer = self.programs["read-word"]
        changed_programs = dict(self.programs)
        changed_programs[producer.name] = replace(
            producer, output_is_boolean=True
        )
        changed_programs = model.validate_programs(changed_programs)
        second = self.plan.sites[1]
        changed_site = replace(
            second,
            activation=model.LogicalActivation(
                model.prior_logical_result("first-read")
            ),
        )
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_plan(
                replace(self.plan, sites=(self.plan.sites[0], changed_site)),
                changed_programs,
            ),
        )

    def test_prior_answer_cannot_enter_child_control_parameter(self):
        consumer = self.programs["value-only-combination"]
        regular = consumer.cases[0]
        controlling = replace(
            consumer,
            route_algorithm="zero-vs-nonzero",
            route_inputs=("prior",),
            cases=(
                replace(regular, tag="nonzero"),
                model.ProgramCase("zero", (), terminal="InactiveControlBranch"),
            ),
        )
        changed = dict(self.programs)
        changed[consumer.name] = controlling
        changed = model.validate_programs(changed)
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.validate_plan(self.plan, changed),
        )

    def test_public_activation_false_suppresses_all_work(self):
        results = model.execute_plan(
            plan=self.plan,
            programs=self.programs,
            inputs={"active": False, "first-index": 2, "second-index": 3},
            oracles=model.freeze_oracles(
                {"first-source": {2: 5}, "second-source": {3: 7}}
            ),
        )
        self.assertFalse(results["second-combination"].active)
        self.assertEqual(results["second-combination"].queries, ())

    def test_independent_core_mutations_fail_before_elaboration(self):
        changed = list(self.events)
        changed[1], changed[2] = changed[2], changed[1]
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.admit_flat_core(tuple(changed)),
        )
        altered = list(self.events)
        event = altered[-2]
        details = tuple(
            (key, ("plan-input:first-index",) if key == "inputs" else value)
            for key, value in event.details
        )
        altered[-2] = replace(event, details=details)
        foreign = model.admit_flat_core(tuple(altered))
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.elaborate(self.plan, self.programs, foreign),
        )

    def test_occurrence_map_accepts_only_causal_target_reorderings(self):
        reordered_events = self.events[4:7] + self.events[:4] + self.events[7:]
        reordered_core = model.admit_flat_core(reordered_events)
        elaboration = model.elaborate(
            self.plan,
            self.programs,
            reordered_core,
        )
        occurrence_map = dict(elaboration.occurrence_map)
        self.assertEqual(
            occurrence_map[("first-read", "only", "source-value", "query")],
            4,
        )
        self.assertEqual(
            occurrence_map[
                ("second-combination", "only", "source-value", "query")
            ],
            1,
        )
        self.assertEqual(
            dict(elaboration.logical_to_source_events),
            {"first-read": (4,), "second-combination": (1,)},
        )
        checked = model.check_elaboration(
            self.plan,
            self.programs,
            reordered_core,
            elaboration,
        )
        self.assertEqual(checked.event_count, 9)

        altered_map = replace(
            elaboration,
            occurrence_map=elaboration.occurrence_map[:-1],
        )
        error = self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.check_elaboration(
                self.plan,
                self.programs,
                reordered_core,
                altered_map,
            ),
        )
        self.assertEqual(error.code, "VDQP-CHECK-006")

        misordered_events = (
            self.events[:2]
            + (self.events[7],)
            + self.events[2:7]
            + self.events[8:]
        )
        error = self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.admit_flat_core(misordered_events),
        )
        self.assertEqual(error.code, "VDQP-CORE-007")

    def test_operational_outcomes_equal_the_foundation_partition(self):
        self.assertEqual(
            {item.value for item in model.OutcomeClass},
            {
                "Unsupported",
                "MissingDependency",
                "CannotAnswer",
                "KindMismatch",
                "Malformed",
                "Refused",
                "DeterministicLimitExceeded",
                "CheckerFailure",
            },
        )


class ProvenanceAndIndependenceTest(unittest.TestCase):
    def test_source_ledger_is_strict_and_primary_source_pinned(self):
        path = HERE / "cases" / "source-ledger.json"
        ledger = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(ledger["schema"], "zkc.verifier-derived-query-plan-sources.v0")
        self.assertEqual(len(ledger["sources"]), 4)
        for source in ledger["sources"]:
            self.assertTrue(source["url"].startswith("https://"))
            self.assertEqual(len(source["sha256"]), 64)
            int(source["sha256"], 16)
            self.assertTrue(source["used_locators"])

    def test_independent_oracle_imports_no_reference_model(self):
        source = inspect.getsource(independent_oracle)
        self.assertNotIn("import model", source)
        self.assertNotIn("from model", source)
        result = independent_oracle.evaluate()
        self.assertEqual(set(result), {"queries", "values"})

    def test_independent_target_imports_no_reference_model(self):
        source = inspect.getsource(independent_target)
        self.assertNotIn("import model", source)
        self.assertNotIn("from model", source)
        self.assertEqual(
            len(independent_target.activation_and_prior_result_events()),
            9,
        )


if __name__ == "__main__":
    unittest.main()
