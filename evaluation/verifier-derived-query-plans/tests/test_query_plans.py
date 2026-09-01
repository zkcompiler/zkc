from __future__ import annotations

from dataclasses import replace
import inspect
import json
from pathlib import Path
import unittest

import independent_oracle
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
            "7861ba7da4cf28e7ef2717e6d4edd01cc54d88304edd4d1745b230c4c1a9d533",
        )
        self.assertEqual(
            model.plan_id(self.plan, self.programs),
            "c692a112493d0457b9dea4c9dd967c5a17af536145b2ef0b269ec208b8a28669",
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
        self.elaboration = model.elaborate(self.plan, self.programs)

    def test_complete_elaboration_checks(self):
        checked = model.check_elaboration(
            self.plan, self.programs, self.elaboration
        )
        self.assertEqual(checked.event_count, 57)
        self.assertEqual(checked.plan_id, self.elaboration.plan_id)

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
            lambda: model.check_elaboration(self.plan, self.programs, candidate),
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
            lambda: model.check_elaboration(self.plan, self.programs, missing),
        )
        events = list(self.elaboration.events)
        events[1], events[2] = events[2], events[1]
        reordered = replace(self.elaboration, events=tuple(events))
        self.assertPlanError(
            model.OutcomeClass.REFUSED,
            lambda: model.check_elaboration(self.plan, self.programs, reordered),
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
            lambda: model.check_elaboration(self.plan, self.programs, candidate),
        )

    def test_wrong_plan_or_target_identity_is_not_reinterpreted(self):
        wrong_plan = replace(self.elaboration, plan_id="00" * 32)
        self.assertPlanError(
            model.OutcomeClass.KIND_MISMATCH,
            lambda: model.check_elaboration(self.plan, self.programs, wrong_plan),
        )
        wrong_target = replace(self.elaboration, target_core_id="11" * 32)
        self.assertPlanError(
            model.OutcomeClass.KIND_MISMATCH,
            lambda: model.check_elaboration(self.plan, self.programs, wrong_target),
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
            model.OutcomeClass.SEMANTIC_FAILURE,
            lambda: self._execute("deep-first-quotient", oracles=absent),
        )

    def test_evaluator_exhaustion_is_noncompletion_not_protocol_rejection(self):
        error = self.assertPlanError(
            model.OutcomeClass.NONCOMPLETION,
            lambda: self._execute("whir-grouped-fold", work_limit=2),
        )
        self.assertEqual(error.boundary, "execution:budget")

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


if __name__ == "__main__":
    unittest.main()
