from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import json
import subprocess
import sys
from types import MappingProxyType
import unittest


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parents[1]
sys.path.insert(0, str(ROOT))

import reference_model as m  # noqa: E402


def coverage_fixture() -> tuple[
    m.BindingCoverageSchema,
    m.BindingCoverageInvocation,
]:
    schema = m.BindingCoverageSchema(
        roles=("imported", "running", "strict"),
        strictly_checked_roles=("strict",),
        digest_edges=(
            m.DigestBindingEdge("imported", "running", "sha256-binding-v1"),
            m.DigestBindingEdge("running", "strict", "sha256-binding-v1"),
        ),
    )
    instances = {
        "imported": m.InstanceOccurrence("imported", "relaxed-r1cs", 11, "i0"),
        "running": m.InstanceOccurrence("running", "relaxed-r1cs", 29, "i1"),
        "strict": m.InstanceOccurrence("strict", "strict-r1cs", 37, "i2"),
    }
    invocation = m.BindingCoverageInvocation(
        MappingProxyType(instances),
        (m.StrictInstanceCheck("strict", instances["strict"], True),),
        tuple(
            m.DigestEquationCheck(
                edge,
                instances[edge.child_role],
                instances[edge.parent_role],
                True,
            )
            for edge in schema.digest_edges
        ),
    )
    return schema, invocation


def family_fixture() -> m.IncrementalCompositionFamily:
    update_verifier = m.CompositionDecisionContract(
        "schema:update-input-v1",
        "schema:update-output-v1",
        "semantics:update-v1",
        "failure-partition:analysis-v1",
    )
    final_decider = m.CompositionDecisionContract(
        "schema:decider-input-v1",
        "schema:decider-output-v1",
        "semantics:decider-v1",
        "failure-partition:analysis-v1",
    )
    return m.IncrementalCompositionFamily(
        members=(
            m.IncrementalCompositionMember(
                "base",
                "protocol-base",
                "plan-base",
                "binding-base",
                "grounding-base",
                "coverage-base",
                (),
                ("base:accumulator",),
            ),
            m.IncrementalCompositionMember(
                "recursive",
                "protocol-recursive",
                "plan-recursive",
                "binding-recursive",
                "grounding-recursive",
                "coverage-recursive",
                ("left-predecessor",),
                ("recursive:accumulator",),
                family_description_advice=m.FamilyDescriptionAdviceContract(
                    "protocol:family-description",
                    "relation:family-description",
                    "grounding-family-description",
                    "sha256-v1",
                    "canonical-json-v1",
                ),
            ),
        ),
        selector_table=(m.SelectorEntry(0, "base"), m.SelectorEntry(1, "recursive")),
        update_verifier=update_verifier,
        final_decider=final_decider,
        carried_obligation_slots=(
            m.CarriedObligationSlot(
                "deferred-final-decision",
                "FieldElement",
                "analysis:run-final-decider",
            ),
        ),
    )


def grounding_fixture(value: int = 41) -> tuple[m.GroundingEquation, m.GroundingInvocation]:
    equation = m.canonical_two_run_recurrence_equation()
    instances = {
        0: m.RelationInstanceOccurrence(
            equation.instance_interfaces[0],
            MappingProxyType({"accumulator": value}),
            "source-instance",
        ),
        1: m.RelationInstanceOccurrence(
            equation.instance_interfaces[1],
            MappingProxyType({"accumulator": value}),
            "target-instance",
        ),
    }
    runs = {
        0: m.QualifiedRunOccurrence(
            equation.run_protocols[0],
            MappingProxyType({"produced_accumulator": value}),
            "source-run",
        ),
        1: m.QualifiedRunOccurrence(
            equation.run_protocols[1],
            MappingProxyType({"statement": value}),
            "target-run",
        ),
    }
    authorities = {
        ("instance", ordinal): m.GroundingSourceAuthority(occurrence)
        for ordinal, occurrence in instances.items()
    }
    authorities.update(
        {
            ("run", ordinal): m.GroundingSourceAuthority(occurrence)
            for ordinal, occurrence in runs.items()
        }
    )
    return equation, m.GroundingInvocation(
        MappingProxyType(instances),
        MappingProxyType(runs),
        MappingProxyType(authorities),
    )


def theorem_fixture(
    *, include_digest_assumption: bool = True,
) -> tuple[
    m.IncrementalCompositionFamily,
    m.CheckedIncrementalCompositionFamily,
    m.IncrementalCompositionTheoremSchema,
    m.TheoremSourceValidation,
]:
    family = family_fixture()
    family_check = m.check_incremental_composition_family(family).value
    assumptions = ["analysis.setup-assumption:transparent-v1"]
    if include_digest_assumption:
        assumptions.extend(
            (
                "analysis.hash-binding-assumption:sha256-binding-v1",
                "analysis.hash-binding-assumption:sha256-v1",
            )
        )
    exact_assumptions = tuple(sorted(assumptions))
    conclusions = (
        m.ConclusionKind.COMPLETENESS,
        m.ConclusionKind.KNOWLEDGE_SOUNDNESS,
        m.ConclusionKind.EFFICIENCY,
    )
    schema = m.IncrementalCompositionTheoremSchema(
        family.identity,
        m.CompositionTopology.PATH,
        1,
        m.ExecutionDepthDomain.ALL_NATURAL_DEPTHS,
        None,
        m.CompliancePredicateDepthDomain.CONSTANT_DEPTH,
        None,
        m.ExperimentModel.STANDARD,
        m.ContinuationQuantifier.ANY_ELIGIBLE_PROVER,
        family.update_verifier.identity,
        family.final_decider.identity,
        (
            "goal:binding-coverage-correspondence:base",
            "goal:binding-coverage-correspondence:recursive",
            "goal:family-description-advice-correspondence:recursive",
            "goal:step-recurrence-correspondence:base",
            "goal:step-recurrence-correspondence:recursive",
        ),
        ("sha256-binding-v1",),
        exact_assumptions,
        (
            m.CarriedObligationBinding(
                "goal:deferred-final-decision",
                "recursive",
                0,
                "recursive:accumulator",
                "analysis:run-final-decider",
            ),
        ),
        conclusions,
    )
    validation = m.TheoremSourceValidation(
        schema.identity,
        "source-validation-bcms-v1",
        m.TheoremTruthTreatment.RETAINED_ASSUMPTION,
    )
    return family, family_check, schema, validation


class BindingCoverageTests(unittest.TestCase):
    def test_complete_acyclic_coverage_is_affirmative(self) -> None:
        schema, invocation = coverage_fixture()
        result = m.check_binding_coverage(schema, invocation)
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(
            result.value.paths_to_strict_check["imported"],
            ("imported", "running", "strict"),
        )
        self.assertEqual(result.value.digest_rule_ids, ("sha256-binding-v1",))

    def test_unbound_imported_instance_is_refused(self) -> None:
        schema, invocation = coverage_fixture()
        schema = replace(schema, digest_edges=schema.digest_edges[1:])
        result = m.check_binding_coverage(schema, invocation)
        self.assertIs(result.outcome, m.Outcome.REFUSED)
        self.assertIn("unbound", result.reason)

    def test_cycle_and_duplicate_parent_are_not_coverage(self) -> None:
        schema, invocation = coverage_fixture()
        cycle = replace(
            schema,
            strictly_checked_roles=("strict",),
            digest_edges=(
                m.DigestBindingEdge("imported", "running", "h"),
                m.DigestBindingEdge("running", "imported", "h"),
            ),
        )
        duplicate = replace(
            schema,
            digest_edges=schema.digest_edges
            + (m.DigestBindingEdge("imported", "strict", "h2"),),
        )
        self.assertIs(m.check_binding_coverage(cycle, invocation).outcome, m.Outcome.REFUSED)
        self.assertIs(m.check_binding_coverage(duplicate, invocation).outcome, m.Outcome.MALFORMED)

    def test_equal_content_different_occurrence_cannot_substitute(self) -> None:
        schema, invocation = coverage_fixture()
        original = invocation.instances["strict"]
        clone = m.InstanceOccurrence(
            original.role,
            original.interface_id,
            original.public_value,
            original.occurrence_label,
        )
        changed = replace(
            invocation,
            strict_checks=(m.StrictInstanceCheck("strict", clone, True),),
        )
        self.assertIs(m.check_binding_coverage(schema, changed).outcome, m.Outcome.REFUSED)

    def test_false_digest_and_false_strict_check_are_negative(self) -> None:
        schema, invocation = coverage_fixture()
        digest_false = replace(
            invocation,
            digest_checks=(replace(invocation.digest_checks[0], affirmative=False),)
            + invocation.digest_checks[1:],
        )
        strict_false = replace(
            invocation,
            strict_checks=(replace(invocation.strict_checks[0], affirmative=False),),
        )
        self.assertIs(m.check_binding_coverage(schema, digest_false).outcome, m.Outcome.NEGATIVE)
        self.assertIs(m.check_binding_coverage(schema, strict_false).outcome, m.Outcome.NEGATIVE)


class IncrementalCompositionFamilyTests(unittest.TestCase):
    def test_closed_family_and_public_selection_are_affirmative(self) -> None:
        family = family_fixture()
        checked = m.check_incremental_composition_family(family)
        self.assertIs(checked.outcome, m.Outcome.AFFIRMATIVE)
        selected = m.select_incremental_composition_member(family, checked.value, 1)
        self.assertIs(selected.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(selected.value.member_key, "recursive")

        forged_check = m.CheckedIncrementalCompositionFamily(
            checked.value.family_id,
            checked.value.member_keys,
            checked.value.selector_values,
            checked.value.family_description_digests,
        )
        self.assertIs(
            m.select_incremental_composition_member(
                family,
                forged_check,
                1,
            ).outcome,
            m.Outcome.REFUSED,
        )

    def test_runtime_structure_dependency_and_generation_are_refused(self) -> None:
        family = family_fixture()
        dependent_member = replace(
            family.members[1],
            runtime_structure_dependencies=("prior-instance.accumulator",),
        )
        dependent = replace(family, members=(family.members[0], dependent_member))
        self.assertIs(
            m.check_incremental_composition_family(dependent).outcome,
            m.Outcome.REFUSED,
        )
        checked = m.check_incremental_composition_family(family).value
        generated = m.select_incremental_composition_member(
            family,
            checked,
            1,
            runtime_generated_structure={"new_core": "from transcript"},
        )
        self.assertIs(generated.outcome, m.Outcome.REFUSED)

    def test_family_description_digest_is_derived_from_the_complete_body(self) -> None:
        family = family_fixture()
        checked = m.check_incremental_composition_family(family)
        self.assertIs(checked.outcome, m.Outcome.AFFIRMATIVE)
        digest = checked.value.family_description_digests["recursive"]
        changed_member = replace(family.members[0], plan_id="plan-base-v2")
        changed = replace(family, members=(changed_member, family.members[1]))
        changed_check = m.check_incremental_composition_family(changed)
        self.assertIs(changed_check.outcome, m.Outcome.AFFIRMATIVE)
        self.assertNotEqual(
            digest,
            changed_check.value.family_description_digests["recursive"],
        )
        self.assertNotIn(
            "external_family_digest",
            m.IncrementalCompositionFamily.__dataclass_fields__,
        )

    def test_self_reference_and_ungrounded_advice_are_refused(self) -> None:
        family = family_fixture()
        embedded_identity = replace(family.members[1], embeds_family_identity=True)
        embedded_digest = replace(
            family.members[1],
            embeds_derived_family_digest=True,
        )
        incomplete_advice = replace(
            family.members[1],
            family_description_advice=replace(
                family.members[1].family_description_advice,
                grounding_equation_id="",
            ),
        )
        for member in (embedded_identity, embedded_digest, incomplete_advice):
            with self.subTest(member=member):
                changed = replace(family, members=(family.members[0], member))
                self.assertIs(
                    m.check_incremental_composition_family(changed).outcome,
                    m.Outcome.REFUSED
                    if member is not incomplete_advice
                    else m.Outcome.MALFORMED,
                )

    def test_selector_table_is_exact_and_cannot_select_unknown_member(self) -> None:
        family = family_fixture()
        incomplete = replace(family, selector_table=family.selector_table[:1])
        duplicate = replace(
            family,
            selector_table=(
                family.selector_table[0],
                replace(family.selector_table[1], selector_value=0),
            ),
        )
        self.assertIs(
            m.check_incremental_composition_family(incomplete).outcome,
            m.Outcome.MALFORMED,
        )
        self.assertIs(
            m.check_incremental_composition_family(duplicate).outcome,
            m.Outcome.MALFORMED,
        )
        checked = m.check_incremental_composition_family(family).value
        self.assertIs(
            m.select_incremental_composition_member(family, checked, 99).outcome,
            m.Outcome.REFUSED,
        )


class GroundingTests(unittest.TestCase):
    def test_exact_two_run_two_instance_grounding_is_affirmative(self) -> None:
        equation, invocation = grounding_fixture()
        result = m.evaluate_two_run_recurrence_grounding(equation, invocation)
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(result.value.source_values, (41, 41, 41, 41))
        self.assertEqual(result.value.agreements, (True, True, True))

    def test_each_equality_is_independently_negative(self) -> None:
        equation, invocation = grounding_fixture()
        changes = (
            ({"produced_accumulator": 42}, invocation.instances, (False, True, True)),
            ({"produced_accumulator": 42}, {
                **invocation.instances,
                0: m.RelationInstanceOccurrence(
                    equation.instance_interfaces[0],
                    MappingProxyType({"accumulator": 42}),
                    "changed-source-instance",
                ),
            }, (True, False, True)),
        )
        for source_values, instances, expected in changes:
            with self.subTest(expected=expected):
                source_run = m.QualifiedRunOccurrence(
                    equation.run_protocols[0],
                    MappingProxyType(source_values),
                    "changed-source-run",
                )
                runs = {**invocation.runs, 0: source_run}
                authorities = {
                    ("instance", ordinal): m.GroundingSourceAuthority(occurrence)
                    for ordinal, occurrence in instances.items()
                }
                authorities.update(
                    {
                        ("run", ordinal): m.GroundingSourceAuthority(occurrence)
                        for ordinal, occurrence in runs.items()
                    }
                )
                changed = m.GroundingInvocation(
                    MappingProxyType(instances),
                    MappingProxyType(runs),
                    MappingProxyType(authorities),
                )
                result = m.evaluate_two_run_recurrence_grounding(equation, changed)
                self.assertIs(result.outcome, m.Outcome.NEGATIVE)
                self.assertEqual(result.value.agreements, expected)
        target_runs = {
            **invocation.runs,
            1: m.QualifiedRunOccurrence(
                equation.run_protocols[1],
                MappingProxyType({"statement": 42}),
                "changed-target-run",
            ),
        }
        authorities = dict(invocation.authorities)
        authorities[("run", 1)] = m.GroundingSourceAuthority(target_runs[1])
        final = m.evaluate_two_run_recurrence_grounding(
            equation,
            replace(
                invocation,
                runs=MappingProxyType(target_runs),
                authorities=MappingProxyType(authorities),
            ),
        )
        self.assertIs(final.outcome, m.Outcome.NEGATIVE)
        self.assertEqual(final.value.agreements, (True, True, False))

    def test_slot_owner_and_occurrence_authority_are_exact(self) -> None:
        equation, invocation = grounding_fixture()
        wrong_owner = replace(
            invocation.instances[0],
            interface_id="relations.other-interface.v1",
        )
        owner_instances = {**invocation.instances, 0: wrong_owner}
        owner_authorities = dict(invocation.authorities)
        owner_authorities[("instance", 0)] = m.GroundingSourceAuthority(wrong_owner)
        owner_result = m.evaluate_two_run_recurrence_grounding(
            equation,
            replace(
                invocation,
                instances=MappingProxyType(owner_instances),
                authorities=MappingProxyType(owner_authorities),
            ),
        )
        self.assertIs(owner_result.outcome, m.Outcome.REFUSED)

        original = invocation.instances[0]
        clone = m.RelationInstanceOccurrence(
            original.interface_id,
            original.public_values,
            original.occurrence_label,
        )
        authority_result = m.evaluate_two_run_recurrence_grounding(
            equation,
            replace(
                invocation,
                authorities=MappingProxyType(
                    {**invocation.authorities, ("instance", 0): m.GroundingSourceAuthority(clone)}
                ),
            ),
        )
        self.assertIs(authority_result.outcome, m.Outcome.REFUSED)

    def test_missing_extra_slots_and_extra_clause_are_refused(self) -> None:
        equation, invocation = grounding_fixture()
        missing = replace(invocation, instances=MappingProxyType({0: invocation.instances[0]}))
        extra = replace(
            invocation,
            runs=MappingProxyType({**invocation.runs, 2: invocation.runs[1]}),
        )
        extra_clause = replace(
            equation,
            equalities=equation.equalities + (m.GroundingEquality(0, 3),),
        )
        self.assertIs(m.evaluate_two_run_recurrence_grounding(equation, missing).outcome, m.Outcome.MALFORMED)
        self.assertIs(m.evaluate_two_run_recurrence_grounding(equation, extra).outcome, m.Outcome.MALFORMED)
        self.assertIs(m.evaluate_two_run_recurrence_grounding(extra_clause, invocation).outcome, m.Outcome.REFUSED)


class TransportAndObligationTests(unittest.TestCase):
    def test_portable_value_is_readmitted_but_has_no_causal_authority(self) -> None:
        pair = m.PortableAccumulatorPair(17, b"private-fold-witness")
        source = m.SourceContinuationOccurrence(pair, "source-output")
        encoded = m.serialize_portable_pair(pair)
        decoded = m.decode_portable_pair(encoded)
        self.assertIs(decoded.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(decoded.value, pair)
        self.assertIsNot(decoded.value, pair)
        validation = m.DeciderResult(decoded.value, True, "protogalaxy-decider-v1")
        readmitted = m.readmit_portable_pair(decoded.value, validation)
        self.assertIs(readmitted.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(m.join_causal_handoff(source, readmitted.value).outcome, m.Outcome.REFUSED)

    def test_live_causal_handoff_is_one_use_and_occurrence_exact(self) -> None:
        pair = m.PortableAccumulatorPair(17, b"w")
        source = m.SourceContinuationOccurrence(pair, "source")
        forged_capability = m.CausalHandoffCapability(source)
        self.assertIs(
            m.issue_causal_handoff(source, forged_capability).outcome,
            m.Outcome.REFUSED,
        )
        capability = m.issue_causal_handoff_capability(source)
        target = m.issue_causal_handoff(source, capability)
        self.assertIs(target.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(m.join_causal_handoff(source, target.value).outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(m.issue_causal_handoff(source, capability).outcome, m.Outcome.REFUSED)
        forged_target = m.CausalTargetInputOccurrence(pair, source, capability)
        self.assertIs(
            m.join_causal_handoff(source, forged_target).outcome,
            m.Outcome.REFUSED,
        )

    def test_decider_must_bind_exact_decoded_occurrence(self) -> None:
        pair = m.PortableAccumulatorPair(17, b"w")
        clone = m.PortableAccumulatorPair(17, b"w")
        result = m.readmit_portable_pair(pair, m.DeciderResult(clone, True, "d"))
        self.assertIs(result.outcome, m.Outcome.REFUSED)

    def test_conditional_report_retains_derived_obligations(self) -> None:
        application = m.apply_incremental_composition_theorem(*theorem_fixture()).value
        judgment = application.judgments[1]
        conditional = m.qualify_verification_report(
            judgment,
            (),
            m.ReportMode.CONDITIONAL,
        )
        self.assertIs(conditional.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(
            conditional.value.outstanding_carried_obligations,
            judgment.outstanding_carried_obligations,
        )
        self.assertIn(
            "goal:deferred-final-decision",
            conditional.value.remaining_hypotheses,
        )

    def test_carried_discharge_does_not_erase_other_hypotheses(self) -> None:
        application = m.apply_incremental_composition_theorem(*theorem_fixture()).value
        judgment = application.judgments[1]
        obligation = judgment.outstanding_carried_obligations[0]
        discharge = m.issue_obligation_discharge(
            obligation,
            obligation.discharge_operation_id,
            True,
            "result:final-decider",
        ).value
        result = m.qualify_verification_report(
            judgment,
            (discharge,),
            m.ReportMode.CARRIED_OBLIGATIONS_DISCHARGED,
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(result.value.outstanding_carried_obligations, ())
        self.assertIn(
            "analysis.setup-assumption:transparent-v1",
            result.value.remaining_hypotheses,
        )

        second_application = m.apply_incremental_composition_theorem(
            *theorem_fixture()
        ).value
        second_judgment = second_application.judgments[1]
        second_obligation = second_judgment.outstanding_carried_obligations[0]
        hypothesis_free = m.qualify_verification_report(
            second_judgment,
            (
                m.issue_obligation_discharge(
                    second_obligation,
                    second_obligation.discharge_operation_id,
                    True,
                    "result:final-decider-2",
                ).value,
            ),
            m.ReportMode.HYPOTHESIS_FREE,
        )
        self.assertIs(hypothesis_free.outcome, m.Outcome.REFUSED)

    def test_hypothesis_free_requires_truth_and_all_assumptions_discharged(self) -> None:
        family, _, schema, _ = theorem_fixture()
        family = replace(
            family,
            members=(
                family.members[0],
                replace(family.members[1], family_description_advice=None),
            ),
        )
        family_check = m.check_incremental_composition_family(family).value
        schema = replace(
            schema,
            family_id=family.identity,
            recurrence_and_coverage_premise_ids=tuple(
                item
                for item in schema.recurrence_and_coverage_premise_ids
                if "family-description-advice" not in item
            ),
            digest_binding_rule_ids=(),
            required_assumption_ids=(),
        )
        validation = m.TheoremSourceValidation(
            schema.identity,
            "source-validation-machine-checked-v1",
            m.TheoremTruthTreatment.ESTABLISHED,
        )
        application = m.apply_incremental_composition_theorem(
            family,
            family_check,
            schema,
            validation,
        ).value
        judgment = application.judgments[0]
        obligation = judgment.outstanding_carried_obligations[0]
        result = m.qualify_verification_report(
            judgment,
            (
                m.issue_obligation_discharge(
                    obligation,
                    obligation.discharge_operation_id,
                    True,
                    "result:established-final-decider",
                ).value,
            ),
            m.ReportMode.HYPOTHESIS_FREE,
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        self.assertEqual(result.value.remaining_hypotheses, ())

    def test_caller_cannot_substitute_or_invent_obligations(self) -> None:
        application = m.apply_incremental_composition_theorem(*theorem_fixture()).value
        judgment = application.judgments[0]
        obligation = judgment.outstanding_carried_obligations[0]
        clone = m.OutstandingCompositionObligation(
            obligation.hypothesis_goal_id,
            obligation.member_key,
            obligation.slot_ordinal,
            obligation.public_coordinate,
            obligation.discharge_operation_id,
        )
        self.assertIs(
            m.issue_obligation_discharge(
                clone,
                clone.discharge_operation_id,
                True,
                "result:forged",
            ).outcome,
            m.Outcome.REFUSED,
        )
        forged_capability = m.ObligationDischargeCapability(
            clone,
            clone.discharge_operation_id,
            True,
            "result:forged",
        )
        substituted = m.qualify_verification_report(
            judgment,
            (
                m.ObligationDischarge(
                    clone,
                    clone.discharge_operation_id,
                    True,
                    "result:forged",
                    forged_capability,
                ),
            ),
            m.ReportMode.CONDITIONAL,
        )
        self.assertIs(substituted.outcome, m.Outcome.REFUSED)

        forged_judgment = m.IncrementalCompositionJudgment(
            judgment.judgment_id,
            judgment.conclusion_kind,
            (),
            (),
        )
        self.assertIs(
            m.qualify_verification_report(
                forged_judgment,
                (),
                m.ReportMode.HYPOTHESIS_FREE,
            ).outcome,
            m.Outcome.REFUSED,
        )


class CycleFoldGuardrailTests(unittest.TestCase):
    def fixture(self) -> tuple[m.PrimaryFoldValues, m.CompanionCurveInstance]:
        step = m.StepOccurrence("cyclefold-step")
        primary = m.PrimaryFoldValues(step, 5, 11, 13, 17)
        companion = m.CompanionCurveInstance(step, (5, 11, 13, 17), True, step, True)
        return primary, companion

    def test_exact_same_step_companion_binding_is_affirmative(self) -> None:
        primary, companion = self.fixture()
        result = m.check_cyclefold_same_step_binding(primary, companion)
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)

    def test_strictness_io_and_same_step_fold_are_all_required(self) -> None:
        primary, companion = self.fixture()
        other_step = m.StepOccurrence(primary.step.step_id)
        mutations = (
            replace(companion, created_in_step=other_step),
            replace(companion, strict=False),
            replace(companion, public_io=(5, 11, 13, 19)),
            replace(companion, folded_in_step=other_step),
            replace(companion, folded_before_completion=False),
            replace(companion, terminal_handoff_only=True),
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                self.assertIsNot(
                    m.check_cyclefold_same_step_binding(primary, mutation).outcome,
                    m.Outcome.AFFIRMATIVE,
                )


class RelationsResultIngressTests(unittest.TestCase):
    def step_sources(self) -> tuple[
        m.CompositionStepResultManifest,
        m.IssuedRelationsResultSource,
        m.IssuedRelationsResultSource,
    ]:
        equation, invocation = grounding_fixture()
        pair = m.PortableAccumulatorPair(41, b"private-step-witness")
        source = m.SourceContinuationOccurrence(pair, "source-continuation")
        causal_capability = m.issue_causal_handoff_capability(source)
        target = m.issue_causal_handoff(source, causal_capability).value
        question = m.CausalStepRecurrenceQuestionCoordinate(
            equation.identity,
            "relations:source-plan-binding",
            "source-export-edge",
            "relations:target-plan-binding",
            "target-ingress-edge",
        )
        recurrence = m.check_causal_step_recurrence(
            question,
            equation,
            invocation,
            source,
            target,
        ).value
        coverage_schema, coverage_invocation = coverage_fixture()
        coverage = m.check_binding_coverage(
            coverage_schema,
            coverage_invocation,
        ).value
        manifest = m.CompositionStepResultManifest(
            question.identity,
            coverage.schema_id,
        )
        recurrence_source = m.issue_causal_step_recurrence_result_source(
            recurrence,
            manifest.identity,
            manifest.purpose_id,
        ).value
        coverage_source = m.issue_binding_coverage_result_source(
            coverage,
            manifest.identity,
            manifest.purpose_id,
        ).value
        return manifest, recurrence_source, coverage_source

    def test_exact_two_slot_owner_local_support_is_affirmative(self) -> None:
        manifest, recurrence_source, coverage_source = self.step_sources()
        result = m.bind_composition_step_result_support(
            manifest,
            recurrence_source,
            coverage_source,
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(result.value.recurrence_source, recurrence_source)
        self.assertIs(result.value.coverage_source, coverage_source)

    def test_forged_result_and_reconstructed_binding_are_refused(self) -> None:
        schema, _invocation = coverage_fixture()
        forged_result = m.CheckedBindingCoverage(
            schema.identity,
            MappingProxyType({"strict": ("strict",)}),
            (),
        )
        self.assertIs(
            m.issue_binding_coverage_result_source(
                forged_result,
                "analysis:consumer",
                "analysis:purpose",
            ).outcome,
            m.Outcome.REFUSED,
        )

        manifest, recurrence_source, coverage_source = self.step_sources()
        rebuilt_binding = replace(coverage_source.binding)
        rebuilt_source = m.IssuedRelationsResultSource(
            rebuilt_binding,
            coverage_source.capability,
        )
        self.assertIs(
            m.bind_composition_step_result_support(
                manifest,
                recurrence_source,
                rebuilt_source,
            ).outcome,
            m.Outcome.REFUSED,
        )

    def test_missing_cross_occurrence_and_wrong_family_slots_are_refused(self) -> None:
        manifest, recurrence_source, coverage_source = self.step_sources()
        changed_manifest = replace(
            manifest,
            coverage_question_coordinate_id="relations:other-coverage-schema",
        )
        self.assertIs(
            m.bind_composition_step_result_support(
                changed_manifest,
                recurrence_source,
                coverage_source,
            ).outcome,
            m.Outcome.REFUSED,
        )
        self.assertIs(
            m.bind_composition_step_result_support(
                manifest,
                recurrence_source,
                recurrence_source,
            ).outcome,
            m.Outcome.REFUSED,
        )

    def test_cyclefold_has_a_separate_one_slot_profile(self) -> None:
        step = m.StepOccurrence("cyclefold-step")
        primary = m.PrimaryFoldValues(step, 5, 11, 13, 17)
        companion = m.CompanionCurveInstance(
            step,
            (5, 11, 13, 17),
            True,
            step,
            True,
        )
        checked = m.check_cyclefold_same_step_binding(primary, companion).value
        coordinate = m.semantic_id(
            "relations.cyclefold-same-step-grounding-question",
            {"step_id": step.step_id},
        )
        manifest = m.CycleFoldResultManifest(coordinate)
        issued = m.issue_cyclefold_same_step_result_source(
            checked,
            coordinate,
            manifest.identity,
            manifest.purpose_id,
        ).value
        self.assertIs(
            m.bind_cyclefold_result_support(manifest, issued).outcome,
            m.Outcome.AFFIRMATIVE,
        )

        step_manifest, recurrence_source, _coverage_source = self.step_sources()
        self.assertIs(
            m.bind_composition_step_result_support(
                step_manifest,
                recurrence_source,
                issued,
            ).outcome,
            m.Outcome.REFUSED,
        )


class TheoremApplicationTests(unittest.TestCase):
    def test_existing_analysis_path_retains_theorem_truth_and_assumptions(self) -> None:
        family, family_check, schema, validation = theorem_fixture()
        result = m.apply_incremental_composition_theorem(
            family,
            family_check,
            schema,
            validation,
        )
        self.assertIs(result.outcome, m.Outcome.AFFIRMATIVE)
        judgment = result.value.judgments[0]
        self.assertIn(
            f"analysis.theorem-truth:{schema.identity}",
            judgment.retained_hypotheses,
        )
        self.assertIn(
            "analysis.hash-binding-assumption:sha256-binding-v1",
            judgment.retained_hypotheses,
        )
        self.assertTrue(result.value.semantic_basis_id)
        self.assertTrue(result.value.support_instantiation_id)
        self.assertTrue(result.value.validation_basis_id)

        forged_check = m.CheckedIncrementalCompositionFamily(
            family_check.family_id,
            family_check.member_keys,
            family_check.selector_values,
            family_check.family_description_digests,
        )
        self.assertIs(
            m.apply_incremental_composition_theorem(
                family,
                forged_check,
                schema,
                validation,
            ).outcome,
            m.Outcome.REFUSED,
        )

    def test_digest_coverage_never_implies_hash_binding(self) -> None:
        result = m.apply_incremental_composition_theorem(
            *theorem_fixture(include_digest_assumption=False)
        )
        self.assertIs(result.outcome, m.Outcome.REFUSED)
        self.assertIn("digest binding assumption", result.reason)

    def test_family_premises_and_carried_obligations_are_owner_derived(self) -> None:
        family, family_check, schema, validation = theorem_fixture()
        missing_premise = replace(
            schema,
            recurrence_and_coverage_premise_ids=(
                schema.recurrence_and_coverage_premise_ids[:-1]
            ),
        )
        missing_binding = replace(schema, carried_obligation_bindings=())
        for mutation, expected_reason in (
            (missing_premise, "correspondence premise"),
            (missing_binding, "obligation set"),
        ):
            with self.subTest(mutation=mutation):
                matching_validation = replace(
                    validation,
                    theorem_schema_id=mutation.identity,
                )
                result = m.apply_incremental_composition_theorem(
                    family,
                    family_check,
                    mutation,
                    matching_validation,
                )
                self.assertIs(result.outcome, m.Outcome.REFUSED)
                self.assertIn(expected_reason, result.reason)

    def test_model_depth_quantifier_and_conclusions_rotate_the_theorem(self) -> None:
        family, family_check, schema, validation = theorem_fixture()
        mutations = (
            replace(schema, topology=m.CompositionTopology.FINITE_IN_DEGREE_DAG),
            replace(schema, maximum_predecessors=2),
            replace(schema, model=m.ExperimentModel.RANDOM_ORACLE),
            replace(
                schema,
                execution_depth_domain=(
                    m.ExecutionDepthDomain.POLYNOMIAL_IN_SECURITY_PARAMETER
                ),
            ),
            replace(
                schema,
                compliance_predicate_depth_domain=(
                    m.CompliancePredicateDepthDomain.POLYNOMIAL_DEPTH
                ),
            ),
            replace(
                schema,
                continuation_quantifier=(
                    m.ContinuationQuantifier.SAME_PROCESS_ACCEPTED_HANDOFF
                ),
            ),
            replace(schema, update_verifier_contract_id="another-update-verifier"),
            replace(schema, final_decider_contract_id="another-final-decider"),
            replace(
                schema,
                digest_binding_rule_ids=("another-binding-v1",),
            ),
            replace(schema, conclusion_kinds=schema.conclusion_kinds[:1]),
        )
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                self.assertNotEqual(mutation.identity, schema.identity)
                result = m.apply_incremental_composition_theorem(
                    family,
                    family_check,
                    mutation,
                    validation,
                )
                self.assertIs(result.outcome, m.Outcome.REFUSED)

        changed_decider = replace(
            schema,
            final_decider_contract_id="another-final-decider",
        )
        changed_decider_validation = replace(
            validation,
            theorem_schema_id=changed_decider.identity,
        )
        changed_decider_result = m.apply_incremental_composition_theorem(
            family,
            family_check,
            changed_decider,
            changed_decider_validation,
        )
        self.assertIs(changed_decider_result.outcome, m.Outcome.REFUSED)
        self.assertIn("final-decider", changed_decider_result.reason)
        wrong_source = replace(validation, theorem_schema_id="another-theorem")
        self.assertIs(
            m.apply_incremental_composition_theorem(
                family,
                family_check,
                schema,
                wrong_source,
            ).outcome,
            m.Outcome.REFUSED,
        )

    def test_finite_live_chain_checks_adjacency_but_cannot_form_theorem(self) -> None:
        run0, run1, run2 = m.LiveRun("r0"), m.LiveRun("r1"), m.LiveRun("r2")
        edges = (
            m.CheckedLiveRecurrenceEdge(run0, run1, "e0"),
            m.CheckedLiveRecurrenceEdge(run1, run2, "e1"),
        )
        chain = m.check_finite_live_chain(edges)
        self.assertIs(chain.outcome, m.Outcome.AFFIRMATIVE)
        self.assertIs(m.form_theorem_from_live_chain(chain.value).outcome, m.Outcome.UNSUPPORTED)
        equal_but_distinct = m.LiveRun("r1")
        broken = replace(edges[1], source=equal_but_distinct)
        self.assertIs(
            m.check_finite_live_chain((edges[0], broken)).outcome,
            m.Outcome.REFUSED,
        )


class PackageIntegrityTests(unittest.TestCase):
    def test_declared_boundary_matrix_matches_executed_outcomes(self) -> None:
        matrix_path = ROOT / "cases" / "expected-boundaries.json"
        body = json.loads(matrix_path.read_text(encoding="utf-8"))

        coverage, coverage_invocation = coverage_fixture()
        unbound = replace(coverage, digest_edges=coverage.digest_edges[1:])
        results: dict[str, tuple[str, str]] = {
            "unbound-imported-instance": (
                m.check_binding_coverage(unbound, coverage_invocation).outcome.value,
                m.check_binding_coverage(coverage, coverage_invocation).outcome.value,
            )
        }

        plan_test = (
            REPOSITORY
            / "evaluation"
            / "plan-continuation-semantics"
            / "tests"
            / "test_relations_and_handoff.py"
        )
        plan_completed = subprocess.run(
            [
                sys.executable,
                "-B",
                str(plan_test),
                "RelationsAndHandoffTests.test_two_distinct_sources_can_supply_one_target_preparation",
            ],
            cwd=REPOSITORY,
            capture_output=True,
            text=True,
            check=False,
        )
        plan_outcome = (
            m.Outcome.AFFIRMATIVE.value
            if plan_completed.returncode == 0
            else "CheckerFailure"
        )
        results["two-distinct-sources-one-target"] = (plan_outcome, plan_outcome)

        pair = m.PortableAccumulatorPair(17, b"portable")
        source = m.SourceContinuationOccurrence(pair, "matrix-source")
        decoded = m.decode_portable_pair(m.serialize_portable_pair(pair))
        readmitted = m.readmit_portable_pair(
            decoded.value,
            m.DeciderResult(decoded.value, True, "matrix-decider"),
        )
        portable_outcome = (
            "AffirmativeReadmissionAndRefusedCausalJoin"
            if readmitted.outcome is m.Outcome.AFFIRMATIVE
            and m.join_causal_handoff(source, readmitted.value).outcome
            is m.Outcome.REFUSED
            else "BoundaryMismatch"
        )
        causal_capability = m.issue_causal_handoff_capability(source)
        causal_target = m.issue_causal_handoff(source, causal_capability)
        causal_outcome = m.join_causal_handoff(source, causal_target.value).outcome.value
        results["serialized-portable-reentry"] = (portable_outcome, causal_outcome)

        family = family_fixture()
        runtime_dependent = replace(
            family,
            members=(
                family.members[0],
                replace(
                    family.members[1],
                    runtime_structure_dependencies=("live:accumulator",),
                ),
            ),
        )
        results["runtime-dependent-target-structure"] = (
            m.check_incremental_composition_family(runtime_dependent).outcome.value,
            m.check_incremental_composition_family(family).outcome.value,
        )

        application = m.apply_incremental_composition_theorem(*theorem_fixture()).value
        judgment = application.judgments[0]
        obligation = judgment.outstanding_carried_obligations[0]
        discharge = m.issue_obligation_discharge(
            obligation,
            obligation.discharge_operation_id,
            True,
            "result:matrix-hypothesis-free",
        ).value
        refused_report = m.qualify_verification_report(
            judgment,
            (discharge,),
            m.ReportMode.HYPOTHESIS_FREE,
        )
        positive_application = m.apply_incremental_composition_theorem(
            *theorem_fixture()
        ).value
        positive_judgment = positive_application.judgments[0]
        positive_obligation = positive_judgment.outstanding_carried_obligations[0]
        positive_discharge = m.issue_obligation_discharge(
            positive_obligation,
            positive_obligation.discharge_operation_id,
            True,
            "result:matrix-carried-clear",
        ).value
        positive_report = m.qualify_verification_report(
            positive_judgment,
            (positive_discharge,),
            m.ReportMode.CARRIED_OBLIGATIONS_DISCHARGED,
        )
        results["hypothesis-free-report-with-retained-hypothesis"] = (
            refused_report.outcome.value,
            positive_report.outcome.value,
        )

        equation, grounding_invocation = grounding_fixture()
        grounding_outcome = m.evaluate_two_run_recurrence_grounding(
            equation,
            grounding_invocation,
        ).outcome.value
        results["exact-two-run-two-instance-grounding"] = (
            grounding_outcome,
            grounding_outcome,
        )

        step = m.StepOccurrence("matrix-cyclefold-step")
        primary = m.PrimaryFoldValues(step, 5, 11, 13, 17)
        companion = m.CompanionCurveInstance(
            step,
            (5, 11, 13, 17),
            True,
            step,
            True,
        )
        results["companion-terminal-handoff-substitution"] = (
            m.check_cyclefold_same_step_binding(
                primary,
                replace(companion, terminal_handoff_only=True),
            ).outcome.value,
            m.check_cyclefold_same_step_binding(primary, companion).outcome.value,
        )

        run0, run1 = m.LiveRun("matrix-r0"), m.LiveRun("matrix-r1")
        live_chain = m.check_finite_live_chain(
            (m.CheckedLiveRecurrenceEdge(run0, run1, "matrix-edge"),)
        )
        theorem_outcome = m.apply_incremental_composition_theorem(
            *theorem_fixture()
        ).outcome.value
        results["finite-live-chain-as-induction-theorem"] = (
            m.form_theorem_from_live_chain(live_chain.value).outcome.value,
            theorem_outcome,
        )

        declared = {item["id"]: item for item in body["cases"]}
        self.assertEqual(set(declared), set(results))
        self.assertEqual(
            len({item["positive_control"] for item in declared.values()}),
            len(declared),
        )
        for case_id, (actual, positive) in results.items():
            with self.subTest(case_id=case_id):
                self.assertEqual(actual, declared[case_id]["expected"])
                self.assertEqual(
                    positive,
                    declared[case_id]["positive_control_expected"],
                )

    def test_source_ledger_has_exact_five_primary_snapshots(self) -> None:
        ledger_path = (
            REPOSITORY
            / "docs-next"
            / "notes"
            / "semantic-revalidation-and-redesign"
            / "semantic-closure-and-freeze"
            / "recursive-composition-boundary"
            / "source-ledger.json"
        )
        body = json.loads(ledger_path.read_text(encoding="utf-8"))
        self.assertEqual(body["schema"], "zkc.recursive-composition-source-ledger.v1")
        self.assertEqual(
            {item["eprint"] for item in body["sources"]},
            {"2020/499", "2023/573", "2023/620", "2023/969", "2023/1106"},
        )
        self.assertEqual(
            {item["eprint"]: item["authors"] for item in body["sources"]},
            {
                "2020/499": (
                    "Benedikt Buenz, Alessandro Chiesa, Pratyush Mishra, "
                    "and Nicholas Spooner"
                ),
                "2023/573": "Abhiram Kothapalli and Srinath Setty",
                "2023/620": "Benedikt Buenz and Binyi Chen",
                "2023/969": "Wilson Nguyen, Dan Boneh, and Srinath Setty",
                "2023/1106": "Liam Eagen and Ariel Gabizon",
            },
        )
        self.assertTrue(
            all(len(item["pdf_sha256"]) == 64 for item in body["sources"])
        )

    def test_owner_plan_model_accepts_two_source_to_one_target_preparation(self) -> None:
        test_file = (
            REPOSITORY
            / "evaluation"
            / "plan-continuation-semantics"
            / "tests"
            / "test_relations_and_handoff.py"
        )
        completed = subprocess.run(
            [
                sys.executable,
                "-B",
                str(test_file),
                "RelationsAndHandoffTests.test_two_distinct_sources_can_supply_one_target_preparation",
            ],
            cwd=REPOSITORY,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)


if __name__ == "__main__":
    unittest.main()
