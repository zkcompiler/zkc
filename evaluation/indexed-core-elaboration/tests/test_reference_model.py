from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import sys
import unittest


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


p = model.protocol


def manual_fri_depth_two_query_one() -> object:
    statement = p.ValueRef.input("statement")
    answer = p.ValueRef.occurrence("answer_0")
    return p.Core(
        inputs=(
            p.InputDecl("statement", p.InputRole.STATEMENT),
            p.InputDecl("session", p.InputRole.PUBLIC_CONTEXT),
            p.InputDecl(
                "field_modulus",
                p.InputRole.PUBLIC_PARAMETER,
                value_sort=p.ValueSort.NAT,
            ),
        ),
        scopes=(p.ScopeDecl("root", None, None),),
        schedule=(
            p.Occurrence(
                "fri_layer_0",
                p.OccurrenceKind.ORACLE_PUBLISH,
                oracle_name="fri_layer_0",
            ),
            p.Occurrence(
                "fold_coin_0",
                p.OccurrenceKind.CHALLENGE,
                dependencies=(statement,),
                challenge_domain=p.ChallengeDomain(97),
            ),
            p.Occurrence(
                "fri_layer_1",
                p.OccurrenceKind.ORACLE_PUBLISH,
                oracle_name="fri_layer_1",
            ),
            p.Occurrence(
                "fold_coin_1",
                p.OccurrenceKind.CHALLENGE,
                dependencies=(statement,),
                challenge_domain=p.ChallengeDomain(98),
            ),
            p.Occurrence(
                "fri_layer_2",
                p.OccurrenceKind.ORACLE_PUBLISH,
                oracle_name="fri_layer_2",
            ),
            p.Occurrence(
                "query_coin_0",
                p.OccurrenceKind.CHALLENGE,
                dependencies=(statement,),
                challenge_domain=p.ChallengeDomain(131),
            ),
            p.Occurrence(
                "query_0",
                p.OccurrenceKind.ORACLE_QUERY,
                dependencies=(p.ValueRef.occurrence("query_coin_0"),),
                oracle_name="fri_layer_2",
            ),
            p.Occurrence(
                "answer_0",
                p.OccurrenceKind.ORACLE_ANSWER,
                dependencies=(p.ValueRef.occurrence("query_0"),),
                oracle_name="fri_layer_2",
            ),
            p.Occurrence(
                "check_0",
                p.OccurrenceKind.CHECK,
                dependencies=(answer, statement),
                check_predicate=p.Predicate(
                    p.PredicateKind.BYTES_EQUAL,
                    (answer, statement),
                ),
            ),
            p.Occurrence("terminal", p.OccurrenceKind.TERMINAL),
        ),
        extensions=("native-oracle-v0",),
        initial_claims=("fri_claim_0",),
        reductions=(
            p.ReductionDecl(
                "fri_reduce_0",
                "check_0",
                "root",
                ("fri_claim_0",),
                (answer, statement),
                ("fold_coin_0", "fold_coin_1", "query_coin_0"),
                (
                    p.RequiredPublication("fri_layer_0", "fold_coin_0"),
                    p.RequiredPublication("fri_layer_1", "fold_coin_1"),
                    p.RequiredPublication("fri_layer_2", "query_coin_0"),
                ),
                ("fri_claim_1",),
            ),
        ),
        claim_uses=(
            p.ClaimConsumerUse("fri_claim_0", "fri_reduce_0"),
            p.ClaimConsumerUse("fri_claim_1", "terminal"),
        ),
    )


def manual_sumcheck_two_rounds() -> object:
    statement = p.ValueRef.input("statement")
    poly0 = p.ValueRef.occurrence("round_poly_0")
    poly1 = p.ValueRef.occurrence("round_poly_1")
    return p.Core(
        inputs=(
            p.InputDecl("statement", p.InputRole.STATEMENT),
            p.InputDecl("session", p.InputRole.PUBLIC_CONTEXT),
            p.InputDecl(
                "field_modulus",
                p.InputRole.PUBLIC_PARAMETER,
                value_sort=p.ValueSort.NAT,
            ),
        ),
        scopes=(p.ScopeDecl("root", None, None),),
        schedule=(
            p.Occurrence("round_poly_0", p.OccurrenceKind.PROVER_MESSAGE),
            p.Occurrence(
                "round_coin_0",
                p.OccurrenceKind.CHALLENGE,
                dependencies=(statement, poly0),
                challenge_domain=p.ChallengeDomain(193),
            ),
            p.Occurrence(
                "round_check_0",
                p.OccurrenceKind.CHECK,
                dependencies=(poly0, statement),
                check_predicate=p.Predicate(
                    p.PredicateKind.BYTES_EQUAL,
                    (poly0, statement),
                ),
            ),
            p.Occurrence("round_poly_1", p.OccurrenceKind.PROVER_MESSAGE),
            p.Occurrence(
                "round_coin_1",
                p.OccurrenceKind.CHALLENGE,
                dependencies=(statement, poly1),
                challenge_domain=p.ChallengeDomain(194),
            ),
            p.Occurrence(
                "round_check_1",
                p.OccurrenceKind.CHECK,
                dependencies=(poly1, statement),
                check_predicate=p.Predicate(
                    p.PredicateKind.BYTES_EQUAL,
                    (poly1, statement),
                ),
            ),
            p.Occurrence("terminal", p.OccurrenceKind.TERMINAL),
        ),
        initial_claims=("sumcheck_claim_0",),
        reductions=(
            p.ReductionDecl(
                "sumcheck_reduce_0",
                "round_check_0",
                "root",
                ("sumcheck_claim_0",),
                (poly0, statement),
                ("round_coin_0",),
                (p.RequiredPublication("round_poly_0", "round_coin_0"),),
                ("sumcheck_claim_1",),
            ),
            p.ReductionDecl(
                "sumcheck_reduce_1",
                "round_check_1",
                "root",
                ("sumcheck_claim_1",),
                (poly1, statement),
                ("round_coin_1",),
                (p.RequiredPublication("round_poly_1", "round_coin_1"),),
                ("sumcheck_claim_2",),
            ),
        ),
        claim_uses=(
            p.ClaimConsumerUse("sumcheck_claim_0", "sumcheck_reduce_0"),
            p.ClaimConsumerUse("sumcheck_claim_1", "sumcheck_reduce_1"),
            p.ClaimConsumerUse("sumcheck_claim_2", "terminal"),
        ),
    )


class SchemaAndIdentityTest(unittest.TestCase):
    def test_interpreter_law_descriptor_is_closed_and_identity_bearing(self) -> None:
        self.assertEqual(
            {item.__name__ for item in model.GRAMMAR_NODE_TYPES},
            {name for name, _ in model.GRAMMAR_NODE_LAWS},
        )
        mutated = tuple(
            (name, law + " with changed mapping")
            if name == "EmitOccurrence"
            else (name, law)
            for name, law in model.GRAMMAR_NODE_LAWS
        )
        self.assertNotEqual(
            model.SCHEMA_PROFILE_ID,
            model.make_schema_profile(mutated).identity,
        )
        changed_formation = tuple(
            law + " with changed admission semantics" if ordinal == 8 else law
            for ordinal, law in enumerate(model.FORMATION_LAWS)
        )
        self.assertNotEqual(
            model.SCHEMA_PROFILE_ID,
            model.make_schema_profile(
                formation_laws=changed_formation,
            ).identity,
        )
        self.assertNotEqual(
            model.make_schema_profile(formation_laws=("alpha|beta",)).identity,
            model.make_schema_profile(formation_laws=("alpha", "beta")).identity,
        )
        with self.assertRaisesRegex(model.GrammarError, "not closed"):
            model.make_schema_profile(model.GRAMMAR_NODE_LAWS[:-1])

    def test_schema_preimage_authenticates_and_all_axes_are_identity_bearing(
        self,
    ) -> None:
        baseline = model.fri_schema()
        self.assertEqual(model.authenticate_schema(baseline), model.schema_id(baseline))
        changed_domain = model.fri_schema(fold_depths=(2, 3))
        changed_bound = model.fri_schema(
            bound=model.ExpansionSize(3, 1, 19, 2, 1, 1, 3, 33)
        )
        changed_program_structure = model.fri_schema(grouped=False)
        self.assertNotEqual(model.schema_id(baseline), model.schema_id(changed_domain))
        self.assertNotEqual(model.schema_id(baseline), model.schema_id(changed_bound))
        self.assertNotEqual(
            model.schema_id(baseline), model.schema_id(changed_program_structure)
        )
        self.assertNotEqual(
            model.schema_id(baseline), model.schema_id(model.sumcheck_schema())
        )

    def test_invalid_missing_extra_reordered_and_out_of_domain_indices_refuse(
        self,
    ) -> None:
        schema = model.fri_schema()
        bad = (
            model.semantic_index(fold_depth=2),
            model.semantic_index(
                query_count=1,
                fold_depth=2,
            ),
            model.semantic_index(
                fold_depth=2,
                query_count=1,
                extra=0,
            ),
            model.semantic_index(
                fold_depth=5,
                query_count=1,
            ),
        )
        for index in bad:
            with (
                self.subTest(index=index),
                self.assertRaises(model.InvalidSemanticIndex),
            ):
                model.check_core_elaboration_at(schema, index)

        oversized = model.SemanticIndex(
            tuple(("fold_depth", 2) for _ in range(model.MAX_AST_SEQUENCE + 1))
        )
        with self.assertRaisesRegex(model.InvalidSemanticIndex, "missing|extra"):
            model.check_core_elaboration_at(schema, oversized)

        malformed = model.SemanticIndex(
            (("fold_depth", 2, "extra"), ("query_count", 1))
        )
        with self.assertRaisesRegex(model.InvalidSemanticIndex, "exact shape"):
            model.check_core_elaboration_at(schema, malformed)

    def test_static_bound_is_semantic_but_evaluator_limit_is_not(self) -> None:
        index = model.semantic_index(
            fold_depth=4,
            query_count=2,
        )
        insufficient = model.fri_schema(
            bound=model.ExpansionSize(3, 1, 17, 2, 1, 1, 3, 33)
        )
        with self.assertRaises(model.StaticExpansionOverflow):
            model.check_core_elaboration_at(insufficient, index)

        schema = model.fri_schema()
        identifier_before = model.schema_id(schema)
        with self.assertRaises(model.EvaluatorLimitExceeded):
            model.check_core_elaboration_at(
                schema,
                index,
                evaluator_limits=model.ExpansionSize(3, 1, 17, 2, 1, 1, 3, 33),
            )
        accepted = model.check_core_elaboration_at(
            schema,
            index,
            evaluator_limits=model.ExpansionSize(3, 1, 18, 2, 1, 1, 3, 33),
        )
        accepted_with_wider_limit = model.check_core_elaboration_at(
            schema,
            index,
            evaluator_limits=model.ExpansionSize(8, 4, 64, 16, 4, 8, 16, 128),
        )
        self.assertEqual(identifier_before, accepted.schema_id)
        self.assertEqual(identifier_before, model.schema_id(schema))
        self.assertEqual(accepted.core_id, accepted_with_wider_limit.core_id)
        self.assertEqual(
            p.core_body(accepted.core),
            p.core_body(accepted_with_wider_limit.core),
        )

    def test_distinct_program_structures_can_name_the_same_exact_core(self) -> None:
        grouped = model.fri_schema(grouped=True)
        flattened = model.fri_schema(grouped=False)
        index = model.semantic_index(fold_depth=3, query_count=2)
        left = model.check_core_elaboration_at(
            grouped,
            index,
        )
        right = model.check_core_elaboration_at(
            flattened,
            index,
        )
        narrow = model.fri_schema(
            fold_depths=(3,),
            query_counts=(2,),
            bound=model.ExpansionSize(3, 1, 16, 2, 1, 1, 3, 31),
        )
        third = model.check_core_elaboration_at(
            narrow,
            index,
        )
        self.assertNotEqual(left.schema_id, right.schema_id)
        self.assertNotEqual(left.schema_id, third.schema_id)
        self.assertEqual(p.core_body(left.core), p.core_body(right.core))
        self.assertEqual(p.core_body(left.core), p.core_body(third.core))
        self.assertEqual(left.core_id, right.core_id)
        self.assertEqual(left.core_id, third.core_id)

    def test_checked_result_is_live_authority_not_a_semantic_subject(self) -> None:
        result = model.check_core_elaboration_at(
            model.sumcheck_schema(),
            model.semantic_index(round_count=1),
        )
        self.assertIs(model.require_live_result(result), result)
        self.assertFalse(hasattr(result, "identity"))
        with self.assertRaises(model.ElaborationError):
            model.CheckedCoreElaborationAt(
                result.schema_id,
                result.index,
                result.core_id,
                result.core,
                result.expansion,
                object(),
            )


class FriFiberTest(unittest.TestCase):
    def test_all_selected_fri_fibers_and_both_program_routes_execute(self) -> None:
        body_by_semantic_fiber: dict[tuple[int, int], bytes] = {}
        for grouped in (True, False):
            schema = model.fri_schema(grouped=grouped)
            indices = model.enumerate_indices(schema)
            self.assertEqual(len(indices), 6)
            for index in indices:
                with self.subTest(grouped=grouped, index=index):
                    checked = model.check_core_elaboration_at(schema, index)
                    p.admit_core(checked.core)
                    pair = model.execute_fresh_fs_pair(checked)
                    self.assertEqual(pair.core_id, checked.core_id)
                    self.assertNotEqual(
                        pair.fresh_protocol_id, pair.fiat_shamir_protocol_id
                    )
                    self.assertTrue(pair.fresh_terminal and pair.fiat_shamir_terminal)
                    key = (index.value("fold_depth"), index.value("query_count"))
                    body = p.core_body(checked.core)
                    if key in body_by_semantic_fiber:
                        self.assertEqual(body_by_semantic_fiber[key], body)
                    body_by_semantic_fiber[key] = body
        self.assertEqual(len(body_by_semantic_fiber), 6)

    def test_hand_authored_fri_core_has_generated_identity(self) -> None:
        checked = model.check_core_elaboration_at(
            model.fri_schema(),
            model.semantic_index(
                fold_depth=2,
                query_count=1,
            ),
        )
        hand_authored = manual_fri_depth_two_query_one()
        p.admit_core(hand_authored)
        self.assertEqual(p.core_body(hand_authored), p.core_body(checked.core))
        self.assertEqual(p.core_id(hand_authored), checked.core_id)

    def test_future_reference_and_last_challenge_anchor_refuse(self) -> None:
        checked = model.check_core_elaboration_at(
            model.fri_schema(),
            model.semantic_index(
                fold_depth=2,
                query_count=1,
            ),
        )
        core = checked.core
        challenge_at = next(
            index
            for index, item in enumerate(core.schedule)
            if item.kind is p.OccurrenceKind.CHALLENGE
        )
        malformed_schedule = list(core.schedule)
        malformed_schedule[challenge_at] = replace(
            malformed_schedule[challenge_at],
            dependencies=(p.ValueRef.occurrence("terminal"),),
        )
        with self.assertRaisesRegex(p.AdmissionError, "prior prefix"):
            p.admit_core(replace(core, schedule=tuple(malformed_schedule)))

        first_reduction = core.reductions[0]
        first_publication = first_reduction.required_publications[0]
        late_anchor = replace(
            first_reduction,
            required_publications=(
                replace(first_publication, next_challenge=None),
                *first_reduction.required_publications[1:],
            ),
        )
        with self.assertRaisesRegex(p.AdmissionError, "least following challenge"):
            p.admit_core(replace(core, reductions=(late_anchor,)))

    def test_late_statement_transcript_frame_refuses_replay(self) -> None:
        checked = model.check_core_elaboration_at(
            model.fri_schema(),
            model.semantic_index(
                fold_depth=2,
                query_count=1,
            ),
        )
        core = checked.core
        construction = p.TranscriptConstruction(b"zkc/indexed-core-elaboration/v1")
        invocation, strategy = model._fiber_runtime_inputs(checked)
        generated = p.generate(
            core,
            construction,
            p.ChallengeInterpretation.FIAT_SHAMIR,
            invocation,
            strategy,
        )
        self.assertIs(type(generated), p.Completed)
        record = generated.record
        statement_at = next(
            index
            for index, frame in enumerate(record.transcript_frames)
            if frame.tag == p.InputRole.STATEMENT.value
        )
        frames = list(record.transcript_frames)
        statement_frame = frames.pop(statement_at)
        frames.append(statement_frame)
        with self.assertRaises(p.ReplayError):
            p.replay(
                core,
                construction,
                invocation,
                p.mutate_record(record, frames=tuple(frames)),
            )


class SumcheckFiberTest(unittest.TestCase):
    def test_all_selected_sumcheck_fibers_admit_and_execute_claim_chains(self) -> None:
        schema = model.sumcheck_schema()
        indices = model.enumerate_indices(schema)
        self.assertEqual(
            tuple(index.value("round_count") for index in indices), (1, 2, 4)
        )
        for index in indices:
            with self.subTest(index=index):
                checked = model.check_core_elaboration_at(schema, index)
                rounds = index.value("round_count")
                self.assertEqual(len(checked.core.reductions), rounds)
                self.assertEqual(
                    tuple(step.input_claims[0] for step in checked.core.reductions),
                    tuple(f"sumcheck_claim_{ordinal}" for ordinal in range(rounds)),
                )
                self.assertEqual(
                    tuple(step.output_claims[0] for step in checked.core.reductions),
                    tuple(f"sumcheck_claim_{ordinal + 1}" for ordinal in range(rounds)),
                )
                pair = model.execute_fresh_fs_pair(checked)
                self.assertTrue(pair.fresh_terminal and pair.fiat_shamir_terminal)

    def test_hand_authored_sumcheck_core_has_generated_identity(self) -> None:
        checked = model.check_core_elaboration_at(
            model.sumcheck_schema(),
            model.semantic_index(round_count=2),
        )
        hand_authored = manual_sumcheck_two_rounds()
        p.admit_core(hand_authored)
        self.assertEqual(p.core_body(hand_authored), p.core_body(checked.core))
        self.assertEqual(p.core_id(hand_authored), checked.core_id)


class ScopeAndNonclaimTest(unittest.TestCase):
    def test_occurrence_clause_measurement_is_exact_but_not_a_generality_claim(
        self,
    ) -> None:
        fri = model.measure_occurrence_authoring(
            model.fri_schema(),
            model.enumerate_indices(model.fri_schema()),
        )
        self.assertEqual(
            fri,
            model.AuthoringMeasurement(6, 84, 8, 76),
        )
        sumcheck = model.measure_occurrence_authoring(
            model.sumcheck_schema(),
            model.enumerate_indices(model.sumcheck_schema()),
        )
        self.assertEqual(
            sumcheck,
            model.AuthoringMeasurement(3, 24, 4, 20),
        )

    def test_finite_fibers_do_not_authorize_an_asymptotic_theorem(self) -> None:
        schema = model.sumcheck_schema()
        checked = tuple(
            model.check_core_elaboration_at(schema, index)
            for index in model.enumerate_indices(schema)
        )
        with self.assertRaisesRegex(model.UnsupportedFamilyClaim, "all-index theorem"):
            model.infer_asymptotic_theorem(schema, checked)


class ClosedGrammarNegativeTest(unittest.TestCase):
    def test_all_expansion_coordinates_have_exact_shape(self) -> None:
        malformed = model.ExpansionSize(3, 1, 13, 4, 0, 1, 5, -1)
        with self.assertRaisesRegex(model.ElaborationError, "exact finite shape"):
            model.admit_schema(model.sumcheck_schema(bound=malformed))

    def test_wide_expression_tuple_is_refused_before_encoding(self) -> None:
        references = tuple(
            model.RefExpression(p.RefKind.INPUT, model.LiteralName(f"v{i}"))
            for i in range(model.MAX_AST_SEQUENCE + 1)
        )
        program = model.CoreProgram(
            (
                model.EmitOccurrence(
                    model.LiteralName("x"),
                    p.OccurrenceKind.ORACLE_PUBLISH,
                    dependencies=references,
                ),
            )
        )
        with self.assertRaisesRegex(model.GrammarError, "width"):
            model.admit_schema(model.sumcheck_schema(program=program))

    def test_deep_name_concatenation_is_refused_before_encoding(self) -> None:
        names = model.ExplicitNames((model.LiteralName("c"),))
        for _ in range(model.MAX_AST_DEPTH + 1):
            names = model.ConcatNames((names,))
        reduction = model.EmitReduction(
            model.LiteralName("r"),
            model.LiteralName("at"),
            model.LiteralName("root"),
            names,
            (),
            model.ExplicitNames(()),
            model.PairedNameSequences(model.ExplicitNames(()), model.ExplicitNames(())),
            model.ExplicitNames(()),
        )
        with self.assertRaisesRegex(model.GrammarError, "depth"):
            model.admit_schema(
                model.sumcheck_schema(program=model.CoreProgram((reduction,)))
            )

    def test_oversized_range_is_refused_for_every_schema_fiber(self) -> None:
        huge = model.RangeNames("claim", model.NatConst(0), model.NatConst(257))
        reduction = model.EmitReduction(
            model.LiteralName("r"),
            model.LiteralName("at"),
            model.LiteralName("root"),
            huge,
            (),
            model.ExplicitNames(()),
            model.PairedNameSequences(model.ExplicitNames(()), model.ExplicitNames(())),
            model.ExplicitNames(()),
        )
        schema = model.IndexedCoreSchema(
            (model.IndexAxis("n", (1, 2)),),
            model.ExpansionSize(0, 0, 0, 1, 0, 0, 0, 1),
            model.CoreProgram((reduction,)),
        )
        with self.assertRaisesRegex(model.EvaluatorLimitExceeded, "range-name"):
            model.admit_schema(schema)

    def test_nested_repeat_work_overflow_refuses_before_interpretation(self) -> None:
        leaf = (model.EmitClaimUse(model.LiteralName("c"), model.LiteralName("x")),)
        commands = leaf
        for ordinal in range(5):
            commands = (model.Repeat("n", f"i{ordinal}", commands),)
        schema = model.IndexedCoreSchema(
            (model.IndexAxis("n", (8,)),),
            model.ExpansionSize(0, 0, 0, 0, 0, 0, 1, 64),
            model.CoreProgram(commands),
        )
        with self.assertRaises(model.StaticExpansionOverflow):
            model.admit_schema(schema)

    def test_command_nesting_bound_is_typed(self) -> None:
        commands = (model.EmitClaimUse(model.LiteralName("c"), model.LiteralName("x")),)
        for _ in range(model.MAX_COMMAND_DEPTH + 1):
            commands = (model.Static(commands),)
        schema = replace(model.sumcheck_schema(), program=model.CoreProgram(commands))
        with self.assertRaisesRegex(model.GrammarError, "depth|nesting"):
            model.admit_schema(schema)

    def test_malformed_command_aggregate_is_rejected(self) -> None:
        malformed = model.CoreProgram(  # type: ignore[arg-type]
            [
                model.EmitOccurrence(
                    model.LiteralName("terminal"),
                    p.OccurrenceKind.TERMINAL,
                )
            ]
        )
        with self.assertRaisesRegex(model.GrammarError, "immutable carrier"):
            model.admit_schema(model.sumcheck_schema(program=malformed))

    def test_repeat_cannot_name_an_unbounded_or_ambient_axis(self) -> None:
        with self.assertRaisesRegex(model.GrammarError, "closed repeat bound"):
            model.admit_schema(model.sumcheck_schema(round_counts=(9,)))

        unbounded = model.CoreProgram(
            (
                model.Repeat(
                    "ambient_size",
                    "item",
                    (
                        model.EmitOccurrence(
                            model.LiteralName("terminal"),
                            p.OccurrenceKind.TERMINAL,
                        ),
                    ),
                ),
            )
        )
        with self.assertRaisesRegex(model.GrammarError, "authenticated finite axis"):
            model.admit_schema(model.sumcheck_schema(program=unbounded))

    def test_finite_index_product_is_bounded_before_program_admission(self) -> None:
        schema = replace(
            model.sumcheck_schema(),
            index_domain=(
                model.IndexAxis("a", (1, 2, 3)),
                model.IndexAxis("b", (1, 2, 3)),
                model.IndexAxis("c", (1, 2, 3)),
                model.IndexAxis("round_count", (1, 2, 4)),
            ),
        )
        with self.assertRaisesRegex(model.ElaborationError, "product"):
            model.admit_schema(schema)

    def test_runtime_dependent_topology_is_explicitly_unsupported(self) -> None:
        dynamic = model.CoreProgram(  # type: ignore[arg-type]
            (
                model.DynamicBranch(
                    model.RefExpression(
                        p.RefKind.INPUT,
                        model.LiteralName("statement"),
                    ),
                    (),
                    (),
                ),
            )
        )
        with self.assertRaises(model.UnsupportedDynamicTopology):
            model.admit_schema(model.sumcheck_schema(program=dynamic))

    def test_publication_zip_length_is_checked_by_generic_interpreter(self) -> None:
        base = model.sumcheck_program()
        repeated = base.commands[1]
        self.assertIs(type(repeated), model.Repeat)
        assert type(repeated) is model.Repeat
        body = list(repeated.commands)
        reduction_at = next(
            index
            for index, command in enumerate(body)
            if type(command) is model.EmitReduction
        )
        reduction = body[reduction_at]
        assert type(reduction) is model.EmitReduction
        body[reduction_at] = replace(
            reduction,
            required_publications=model.PairedNameSequences(
                reduction.required_publications.publications,
                model.ExplicitNames(()),
            ),
        )
        malformed = replace(
            base,
            commands=(
                base.commands[0],
                replace(repeated, commands=tuple(body)),
                base.commands[2],
            ),
        )
        schema = model.sumcheck_schema(program=malformed)
        with self.assertRaisesRegex(model.GrammarError, "unequal lengths"):
            model.elaborate_core_candidate(
                schema,
                model.semantic_index(round_count=1),
            )


if __name__ == "__main__":
    unittest.main()
