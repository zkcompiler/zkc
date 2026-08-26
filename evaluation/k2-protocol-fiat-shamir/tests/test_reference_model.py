from __future__ import annotations

from dataclasses import FrozenInstanceError, replace
import hashlib
from pathlib import Path
import sys
from types import MappingProxyType
import unittest
from unittest import mock


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

import reference_model as model  # noqa: E402


def completed(result: model.GenerationResult) -> model.RunRecord:
    if type(result) is not model.Completed:
        raise AssertionError(result)
    return result.record


def terminal_claims(
    name: str = "terminal",
) -> tuple[
    tuple[str, ...],
    tuple[model.ReductionDecl, ...],
    tuple[model.ClaimConsumerUse, ...],
]:
    return ("claim",), (), (model.ClaimConsumerUse("claim", name),)


def core_with(
    schedule: tuple[model.Occurrence, ...],
    *,
    inputs: tuple[model.InputDecl, ...] = (),
    scopes: tuple[model.ScopeDecl, ...] = (model.ScopeDecl("root", None, None),),
    extensions: tuple[str, ...] = (),
) -> model.Core:
    claims, reductions, uses = terminal_claims(schedule[-1].name)
    return model.Core(
        inputs=inputs,
        scopes=scopes,
        schedule=schedule,
        extensions=extensions,
        initial_claims=claims,
        reductions=reductions,
        claim_uses=uses,
    )


def invocation(values: dict[str, model.Value]) -> model.Invocation:
    return model.Invocation(MappingProxyType(dict(values)))


def construction(label: bytes = b"zkc/k2/test/v0", **kwargs: object) -> model.TranscriptConstruction:
    return model.TranscriptConstruction(label, **kwargs)  # type: ignore[arg-type]


class CanonicalFrameContractVectorTest(unittest.TestCase):
    def setUp(self) -> None:
        self.element_type = model.k1.ValueType(
            model.k1.BYTES_DOMAIN,
            model.k1.BytesSchema(0, 32),
        )
        self.result_type = model.appendix_oracle_lookup_result_type(
            self.element_type
        )

    def _assert_oracle_answer_vector(self, answer: object) -> object:
        body = model.appendix_oracle_answer_frame_body(
            7,
            3,
            self.element_type,
            answer,
        )
        self.assertIs(type(body), model.k1.DatumVariant)
        self.assertEqual(body.case, 10)
        self.assertIs(type(body.payload), model.k1.DatumRecord)
        self.assertEqual(
            body.payload.fields,
            (
                (0, model.k1.Nat(7)),
                (1, model.k1.Nat(3)),
                (2, model.k1.value_type_datum(self.result_type)),
                (3, answer),
            ),
        )
        self.assertEqual(
            model.k1.decode_datum(model.k1.encode_datum(body)),
            body,
        )
        self.assertEqual(
            model.k1.admit_value(self.result_type, answer).datum,
            answer,
        )
        return body

    def test_guard_outcome_uses_exact_k1_boolean_scalars(self) -> None:
        for active, scalar_bytes in ((False, b"\x01"), (True, b"\x02")):
            with self.subTest(active=active):
                body = model.appendix_guard_outcome_frame_body(9, active)
                self.assertIs(type(body), model.k1.DatumVariant)
                self.assertEqual(body.case, 5)
                self.assertIs(type(body.payload), model.k1.DatumRecord)
                self.assertEqual(body.payload.fields, ((0, model.k1.Nat(9)), (1, active)))
                self.assertIs(type(body.payload.fields[1][1]), bool)
                self.assertEqual(model.k1.encode_datum(active), scalar_bytes)
                self.assertEqual(
                    model.k1.decode_datum(model.k1.encode_datum(body)),
                    body,
                )
                with self.assertRaisesRegex(
                    model.ModelError,
                    "exact K1 Boolean",
                ):
                    model.appendix_guard_outcome_frame_body(
                        9,
                        model.k1.DatumVariant(0, active),  # type: ignore[arg-type]
                    )

    def test_oracle_answer_absent_uses_lookup_result_type(self) -> None:
        absent = model.k1.DatumVariant(0, model.k1.UNIT)
        self._assert_oracle_answer_vector(absent)
        with self.assertRaises(model.k1.ValueAdmissionRefusedError):
            model.k1.admit_value(self.element_type, absent)

    def test_oracle_answer_present_uses_lookup_result_type(self) -> None:
        element = model.k1.BytesValue(b"answer")
        present = model.k1.DatumVariant(1, element)
        present_body = self._assert_oracle_answer_vector(present)
        with self.assertRaises(model.k1.ValueAdmissionRefusedError):
            model.k1.admit_value(self.element_type, present)
        with self.assertRaises(model.k1.ValueAdmissionRefusedError):
            model.k1.admit_value(self.result_type, element)
        absent_body = model.appendix_oracle_answer_frame_body(
            7,
            3,
            self.element_type,
            model.k1.DatumVariant(0, model.k1.UNIT),
        )
        self.assertNotEqual(
            model.k1.encode_datum(absent_body),
            model.k1.encode_datum(present_body),
        )


class SchnorrPairTest(unittest.TestCase):
    def setUp(self) -> None:
        self.core, self.construction, self.invocation, self.strategy = model.schnorr_fixture()

    def test_same_literal_core_fresh_and_fs_both_accept(self) -> None:
        fresh = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                self.strategy,
                fresh_resolver=model.ScriptedFreshResolver({"challenge": 7}),
            )
        )
        fs = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                self.invocation,
                self.strategy,
            )
        )
        self.assertIs(fresh.entries[-1].value, True)
        self.assertIs(fs.entries[-1].value, True)
        self.assertEqual(fresh.core_id, fs.core_id)
        self.assertIsNone(fresh.construction_id)
        self.assertEqual(fresh.transcript_frames, ())
        self.assertIsNone(fresh.terminal_state)
        self.assertTrue(
            all(
                entry.prefix_state is None
                and not entry.draw_namespaces
                and entry.sampling_attempts is None
                for entry in fresh.entries
            )
        )
        self.assertEqual(
            fs.construction_id,
            model.construction_id(self.core, self.construction),
        )
        evidence = model.check_fresh_fs_pair(
            self.core,
            self.construction,
            self.invocation,
            fresh,
            fs,
        )
        self.assertTrue(evidence.fresh_terminal)
        self.assertTrue(evidence.fiat_shamir_terminal)

    def test_generated_records_replay_exactly(self) -> None:
        for interpretation in model.ChallengeInterpretation:
            with self.subTest(interpretation=interpretation):
                record = completed(
                    model.generate(
                        self.core,
                        self.construction,
                        interpretation,
                        self.invocation,
                        self.strategy,
                        fresh_resolver=(
                            model.ScriptedFreshResolver({"challenge": 7})
                            if interpretation is model.ChallengeInterpretation.FRESH
                            else None
                        ),
                    )
                )
                self.assertEqual(
                    model.replay(
                        self.core,
                        self.construction,
                        self.invocation,
                        record,
                    ),
                    record,
                )

    def test_construction_identity_is_scoped_to_one_core(self) -> None:
        changed = replace(
            self.core,
            schedule=(
                replace(self.core.schedule[0], name="different_commitment"),
                self.core.schedule[1],
                self.core.schedule[2],
                self.core.schedule[3],
                self.core.schedule[4],
            ),
        )
        # Repair references so both Cores are admitted and differ semantically.
        changed = replace(
            changed,
            schedule=(
                changed.schedule[0],
                changed.schedule[1],
                changed.schedule[2],
                replace(
                    changed.schedule[3],
                    dependencies=(
                        model.ValueRef.input("g"),
                        model.ValueRef.input("statement"),
                        model.ValueRef.occurrence("different_commitment"),
                        model.ValueRef.occurrence("challenge"),
                        model.ValueRef.occurrence("response"),
                        model.ValueRef.input("p"),
                    ),
                    check_predicate=replace(
                        changed.schedule[3].check_predicate,
                        refs=(
                            model.ValueRef.input("g"),
                            model.ValueRef.input("statement"),
                            model.ValueRef.occurrence("different_commitment"),
                            model.ValueRef.occurrence("challenge"),
                            model.ValueRef.occurrence("response"),
                            model.ValueRef.input("p"),
                        ),
                    ),
                ),
                changed.schedule[4],
            ),
            reductions=(
                replace(
                    changed.reductions[0],
                    side_inputs=tuple(
                        model.ValueRef.occurrence("different_commitment")
                        if ref == model.ValueRef.occurrence("commitment")
                        else ref
                        for ref in changed.reductions[0].side_inputs
                    ),
                    required_publications=(
                        model.RequiredPublication(
                            "different_commitment",
                            "challenge",
                        ),
                        model.RequiredPublication("response", None),
                    ),
                ),
            ),
        )
        self.assertNotEqual(
            model.construction_id(self.core, self.construction),
            model.construction_id(changed, self.construction),
        )

    def test_fresh_replay_does_not_attach_or_validate_a_construction(self) -> None:
        fresh = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                self.strategy,
                fresh_resolver=model.ScriptedFreshResolver({"challenge": 7}),
            )
        )
        deliberately_unsupported = replace(
            self.construction,
            version="unsupported-unused-construction",
        )
        self.assertEqual(
            model.replay(
                self.core,
                deliberately_unsupported,
                self.invocation,
                fresh,
            ),
            fresh,
        )

    def test_strategy_future_read_is_noncompletion_but_record_replays(self) -> None:
        valid = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                self.invocation,
                self.strategy,
            )
        )

        class FutureReader:
            def move(self, occurrence: model.Occurrence, view: model.ProverView) -> model.Value:
                if occurrence.name == "commitment":
                    return view.read_occurrence("response")
                return 0

        result = model.generate(
            self.core,
            self.construction,
            model.ChallengeInterpretation.FIAT_SHAMIR,
            self.invocation,
            FutureReader(),
        )
        self.assertEqual(
            result,
            model.Noncompletion(
                model.NoncompletionReason.FUTURE_READ,
                "commitment",
                "occurrence 'response' is not in the current prefix",
            ),
        )
        self.assertEqual(
            model.replay(self.core, self.construction, self.invocation, valid),
            valid,
        )

    def test_fresh_coin_is_resolved_only_at_its_challenge(self) -> None:
        self.assertFalse(hasattr(self.invocation, "public_coins"))
        resolver = model.ScriptedFreshResolver({"challenge": 7})

        def commitment(_: model.ProverView) -> model.Value:
            self.assertEqual(resolver.requests, ())
            return pow(2, 4, 23)

        def response(view: model.ProverView) -> model.Value:
            self.assertEqual(
                tuple(request.occurrence for request in resolver.requests),
                ("challenge",),
            )
            challenge = view.read_occurrence("challenge")
            assert type(challenge) is int
            return (4 + challenge * 3) % 11

        record = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                model.ScriptedStrategy(
                    {"commitment": commitment, "response": response}
                ),
                fresh_resolver=resolver,
            )
        )
        self.assertIs(record.entries[-1].value, True)

    def test_fresh_resolver_value_does_not_change_invocation_identity(self) -> None:
        first = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                self.strategy,
                fresh_resolver=model.ScriptedFreshResolver({"challenge": 7}),
            )
        )
        second = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                self.strategy,
                fresh_resolver=model.ScriptedFreshResolver({"challenge": 8}),
            )
        )
        self.assertEqual(first.invocation_id, second.invocation_id)
        self.assertNotEqual(first.entries[1].value, second.entries[1].value)
        self.assertNotEqual(first, second)

    def test_fresh_generation_refuses_missing_or_invalid_resolution(self) -> None:
        class ConstantResolver:
            def __init__(self, value: object) -> None:
                self.value = value

            def resolve(self, _: model.FreshChallengeRequest) -> int:
                return self.value  # type: ignore[return-value]

        cases = (
            ("missing resolver", None, "needs a resolver"),
            (
                "missing challenge value",
                model.ScriptedFreshResolver({}),
                "has no value",
            ),
            ("non-integer value", ConstantResolver(b"bad"), "non-integer"),
            (
                "out-of-domain value",
                model.ScriptedFreshResolver({"challenge": 11}),
                "outside the declared domain",
            ),
        )
        for label, resolver, message in cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(model.FreshResolutionError, message):
                    model.generate(
                        self.core,
                        self.construction,
                        model.ChallengeInterpretation.FRESH,
                        self.invocation,
                        self.strategy,
                        fresh_resolver=resolver,
                    )

    def test_strategy_stop_is_not_a_core_terminal(self) -> None:
        result = model.generate(
            self.core,
            self.construction,
            model.ChallengeInterpretation.FRESH,
            self.invocation,
            model.ScriptedStrategy({}),
        )
        self.assertIs(type(result), model.Noncompletion)
        assert type(result) is model.Noncompletion
        self.assertIs(result.reason, model.NoncompletionReason.STRATEGY_STOPPED)
        self.assertNotIn("ProverDidNotProduce", tuple(item.value for item in model.OccurrenceKind))

    def test_bad_response_replays_as_rejected_not_as_causal_evidence(self) -> None:
        fresh = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                model.ScriptedStrategy({"commitment": 1, "response": 1}),
                fresh_resolver=model.ScriptedFreshResolver({"challenge": 7}),
            )
        )
        self.assertIs(fresh.entries[-1].value, False)
        self.assertEqual(
            model.replay(self.core, self.construction, self.invocation, fresh),
            fresh,
        )


class StrongFiatShamirBindingTest(unittest.TestCase):
    def setUp(self) -> None:
        self.core, self.construction, self.invocation, self.strategy = model.schnorr_fixture()
        self.record = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                self.invocation,
                self.strategy,
            )
        )

    def test_initialization_headers_and_root_bindings_have_exact_order(self) -> None:
        frames = self.record.transcript_frames
        self.assertEqual(
            tuple(frame.tag for frame in frames[:4]),
            (
                "core-header",
                "construction-header",
                "application-domain",
                "scope-open",
            ),
        )
        self.assertEqual(frames[0].payload, model.core_id(self.core).internal_reference())
        self.assertEqual(
            frames[1].payload,
            model.construction_id(self.core, self.construction).internal_reference(),
        )
        self.assertEqual(frames[2].payload, self.construction.application_domain)
        binding_tags = tuple(frame.tag for frame in frames[4:9])
        self.assertEqual(
            binding_tags,
            (
                "public-parameter",
                "public-parameter",
                "public-parameter",
                "statement",
                "public-context",
            ),
        )
        self.assertNotIn("guard-outcome", tuple(frame.tag for frame in frames))

    def test_omitted_statement_is_rejected_at_invocation_boundary(self) -> None:
        values = dict(self.invocation.values)
        del values["statement"]
        with self.assertRaisesRegex(model.InvocationError, "exactly every"):
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                invocation(values),
                self.strategy,
            )

    def test_substituted_statement_changes_invocation_and_replay_fails(self) -> None:
        values = dict(self.invocation.values)
        values["statement"] = 1
        changed = invocation(values)
        self.assertNotEqual(
            model.invocation_id(self.core, changed),
            self.record.invocation_id,
        )
        with self.assertRaisesRegex(model.ReplayError, "identity axes"):
            model.replay(self.core, self.construction, changed, self.record)

    def test_missing_or_late_statement_frame_is_rejected(self) -> None:
        statement_at = next(
            index for index, frame in enumerate(self.record.transcript_frames) if frame.tag == "statement"
        )
        missing = self.record.transcript_frames[:statement_at] + self.record.transcript_frames[statement_at + 1 :]
        with self.assertRaisesRegex(model.ReplayError, "exact derived"):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(self.record, frames=missing),
            )
        late = list(self.record.transcript_frames)
        frame = late.pop(statement_at)
        late.append(frame)
        with self.assertRaisesRegex(model.ReplayError, "exact derived"):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(self.record, frames=tuple(late)),
            )

    def test_wire_only_or_missing_prover_influence_is_impossible(self) -> None:
        self.assertEqual(
            model.required_influence_kinds(self.core.schedule[0]),
            ("prover-message",),
        )
        index = next(
            index
            for index, frame in enumerate(self.record.transcript_frames)
            if frame.tag == "prover-message"
        )
        frames = self.record.transcript_frames[:index] + self.record.transcript_frames[index + 1 :]
        with self.assertRaises(model.ReplayError):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(self.record, frames=frames),
            )

    def test_reordered_required_influence_is_rejected(self) -> None:
        frames = list(self.record.transcript_frames)
        first = next(i for i, item in enumerate(frames) if item.tag == "prover-message")
        second = next(
            i
            for i in range(first + 1, len(frames))
            if frames[i].tag == "prover-message"
        )
        frames[first], frames[second] = frames[second], frames[first]
        with self.assertRaises(model.ReplayError):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(self.record, frames=tuple(frames)),
            )

    def test_exact_challenge_prefix_is_checked(self) -> None:
        challenge_at = next(
            i for i, entry in enumerate(self.record.entries) if entry.kind is model.OccurrenceKind.CHALLENGE
        )
        entries = list(self.record.entries)
        entries[challenge_at] = replace(entries[challenge_at], prefix_state=b"\x00" * 32)
        with self.assertRaises(model.ReplayError):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(self.record, entries=tuple(entries)),
            )

    def test_influence_comparison_covers_condition_and_reduction_publication(self) -> None:
        challenge = next(
            entry
            for entry in self.record.entries
            if entry.occurrence == "challenge"
        )
        self.assertIsNotNone(challenge.influence)
        assert challenge.influence is not None
        self.assertEqual(challenge.influence.missing, ())
        required = set(challenge.influence.required)
        self.assertIn(
            model.InfluenceAtom(
                "challenge-condition",
                ("challenge", "input", "statement"),
            ),
            required,
        )
        self.assertIn(
            model.InfluenceAtom("prover-message", ("commitment",)),
            required,
        )

    def test_influence_comparison_is_an_ordered_subtrace(self) -> None:
        first = model.InfluenceAtom("prover-message", ("first",))
        second = model.InfluenceAtom("prover-message", ("second",))
        extra = model.InfluenceAtom("scope-open", ("root",))

        positive = model.compare_influence(
            (first, second),
            (extra, first, second),
        )
        self.assertEqual(positive.required, (first, second))
        self.assertEqual(positive.observed, (extra, first, second))
        self.assertEqual(positive.missing, ())

        reversed_trace = model.compare_influence(
            (first, second),
            (second, first),
        )
        self.assertEqual(reversed_trace.required, (first, second))
        self.assertEqual(reversed_trace.observed, (second, first))
        self.assertEqual(reversed_trace.missing, (second,))

    def test_duplicate_frame_is_rejected_as_duplicate_influence(self) -> None:
        index = next(
            i
            for i, frame in enumerate(self.record.transcript_frames)
            if frame.tag == "prover-message"
        )
        frames = (
            self.record.transcript_frames[: index + 1]
            + (self.record.transcript_frames[index],)
            + self.record.transcript_frames[index + 1 :]
        )
        with self.assertRaisesRegex(model.ReplayError, "duplicate transcript influence"):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(self.record, frames=frames),
            )

    def test_path_skip_framing_is_mandatory_for_conditional_message(self) -> None:
        core = core_with(
            (
                model.Occurrence(
                    "conditional",
                    model.OccurrenceKind.PROVER_MESSAGE,
                    guard=model.Predicate(
                        model.PredicateKind.BOOL,
                        (model.ValueRef.input("enabled"),),
                    ),
                ),
                model.Occurrence(
                    "challenge",
                    model.OccurrenceKind.CHALLENGE,
                    challenge_domain=model.ChallengeDomain(11),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl("statement", model.InputRole.STATEMENT),
                model.InputDecl(
                    "enabled",
                    model.InputRole.PUBLIC_CONTEXT,
                    value_sort=model.ValueSort.BOOL,
                ),
            ),
        )
        inv = invocation({"statement": b"s", "enabled": False})
        record = completed(
            model.generate(
                core,
                construction(b"conditional"),
                model.ChallengeInterpretation.FIAT_SHAMIR,
                inv,
                model.ScriptedStrategy({}),
            )
        )
        self.assertIs(record.entries[0].status, model.EntryStatus.SKIPPED)
        self.assertNotIn("prover-message", tuple(frame.tag for frame in record.transcript_frames))
        path_at = next(
            i
            for i, frame in enumerate(record.transcript_frames)
            if frame.tag == "guard-outcome" and b"conditional" in frame.payload
        )
        frames = record.transcript_frames[:path_at] + record.transcript_frames[path_at + 1 :]
        with self.assertRaises(model.ReplayError):
            model.replay(
                core,
                construction(b"conditional"),
                inv,
                model.mutate_record(record, frames=frames),
            )

    def test_executed_conditional_message_is_mandatory_influence(self) -> None:
        core = core_with(
            (
                model.Occurrence(
                    "conditional",
                    model.OccurrenceKind.PROVER_MESSAGE,
                    guard=model.Predicate(
                        model.PredicateKind.BOOL,
                        (model.ValueRef.input("enabled"),),
                    ),
                ),
                model.Occurrence(
                    "challenge",
                    model.OccurrenceKind.CHALLENGE,
                    challenge_domain=model.ChallengeDomain(11),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl("statement", model.InputRole.STATEMENT),
                model.InputDecl(
                    "enabled",
                    model.InputRole.PUBLIC_CONTEXT,
                    value_sort=model.ValueSort.BOOL,
                ),
            ),
        )
        inv = invocation({"statement": b"s", "enabled": True})
        record = completed(
            model.generate(
                core,
                construction(b"conditional-on"),
                model.ChallengeInterpretation.FIAT_SHAMIR,
                inv,
                model.ScriptedStrategy({"conditional": b"proof"}),
            )
        )
        self.assertIn("prover-message", tuple(frame.tag for frame in record.transcript_frames))
        self.assertEqual(
            tuple(frame.tag for frame in record.transcript_frames).count(
                "guard-outcome"
            ),
            1,
        )


class PublicCoinAndNamespaceTest(unittest.TestCase):
    def test_verifier_private_input_blocks_fs_but_not_fresh(self) -> None:
        core = core_with(
            (
                model.Occurrence(
                    "challenge",
                    model.OccurrenceKind.CHALLENGE,
                    dependencies=(model.ValueRef.input("private"),),
                    challenge_domain=model.ChallengeDomain(7),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(model.InputDecl("private", model.InputRole.VERIFIER_PRIVATE),),
        )
        inv = invocation({"private": b"secret"})
        self.assertFalse(model.is_public_coin_eligible(core))
        fresh = completed(
            model.generate(
                core,
                construction(b"private"),
                model.ChallengeInterpretation.FRESH,
                inv,
                model.ScriptedStrategy({}),
                fresh_resolver=model.ScriptedFreshResolver({"challenge": 2}),
            )
        )
        self.assertIs(fresh.entries[-1].value, True)
        with self.assertRaisesRegex(model.AdmissionError, "public-coin"):
            model.generate(
                core,
                construction(b"private"),
                model.ChallengeInterpretation.FIAT_SHAMIR,
                inv,
                model.ScriptedStrategy({}),
            )

    def test_unused_verifier_private_input_does_not_block_fs(self) -> None:
        core = core_with(
            (
                model.Occurrence(
                    "challenge",
                    model.OccurrenceKind.CHALLENGE,
                    challenge_domain=model.ChallengeDomain(7),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl(
                    "unused-private",
                    model.InputRole.VERIFIER_PRIVATE,
                ),
            ),
        )
        inv = invocation({"unused-private": b"secret"})
        self.assertTrue(model.is_public_coin_eligible(core))
        record = completed(
            model.generate(
                core,
                construction(b"unused-private"),
                model.ChallengeInterpretation.FIAT_SHAMIR,
                inv,
                model.ScriptedStrategy({}),
            )
        )
        self.assertIs(record.entries[-1].value, True)

    def test_private_guard_on_public_prover_activity_blocks_fs(self) -> None:
        core = core_with(
            (
                model.Occurrence(
                    "conditional-publication",
                    model.OccurrenceKind.PROVER_MESSAGE,
                    guard=model.Predicate(
                        model.PredicateKind.BOOL,
                        (model.ValueRef.input("private"),),
                    ),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl(
                    "private",
                    model.InputRole.VERIFIER_PRIVATE,
                    value_sort=model.ValueSort.BOOL,
                ),
            ),
        )
        inv = invocation({"private": False})
        self.assertFalse(model.is_public_coin_eligible(core))
        fresh = completed(
            model.generate(
                core,
                construction(b"private-guard"),
                model.ChallengeInterpretation.FRESH,
                inv,
                model.ScriptedStrategy({}),
            )
        )
        self.assertIs(fresh.entries[-1].value, True)
        with self.assertRaisesRegex(model.AdmissionError, "public-coin"):
            model.generate(
                core,
                construction(b"private-guard"),
                model.ChallengeInterpretation.FIAT_SHAMIR,
                inv,
                model.ScriptedStrategy({}),
            )

    def test_nonpublic_verifier_move_blocks_fs(self) -> None:
        core = core_with(
            (
                model.Occurrence(
                    "secret-derived",
                    model.OccurrenceKind.VERIFIER_MESSAGE,
                    dependencies=(model.ValueRef.input("private"),),
                    verifier_rule=model.VerifierRule(
                        model.VerifierRuleKind.COPY,
                    ),
                ),
                model.Occurrence(
                    "challenge",
                    model.OccurrenceKind.CHALLENGE,
                    dependencies=(model.ValueRef.occurrence("secret-derived"),),
                    challenge_domain=model.ChallengeDomain(7),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl("private", model.InputRole.VERIFIER_PRIVATE),
            ),
        )
        self.assertFalse(model.is_public_coin_eligible(core))
        with self.assertRaises(model.AdmissionError):
            model.generate(
                core,
                construction(b"nonpublic"),
                model.ChallengeInterpretation.FIAT_SHAMIR,
                invocation({"private": b"secret"}),
                model.ScriptedStrategy({}),
            )

    def test_two_challenge_namespaces_are_derived_and_distinct(self) -> None:
        core = core_with(
            (
                model.Occurrence("c1", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(7)),
                model.Occurrence("c2", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(7)),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            )
        )
        tc = construction(b"namespaces")
        first = model.derive_occurrence_namespace(core, tc, 0)
        second = model.derive_occurrence_namespace(core, tc, 1)
        self.assertNotEqual(first, second)
        first_datum = model.k1.decode_datum(first)
        self.assertEqual(first_datum.fields[3][1], model.k1.Nat(0))

    def test_duplicate_namespace_record_mutation_is_rejected(self) -> None:
        core = core_with(
            (
                model.Occurrence("c1", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(7)),
                model.Occurrence("c2", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(7)),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            )
        )
        inv = invocation({})
        tc = construction(b"namespace-mutation")
        fresh = completed(
            model.generate(
                core,
                tc,
                model.ChallengeInterpretation.FRESH,
                inv,
                model.ScriptedStrategy({}),
                fresh_resolver=model.ScriptedFreshResolver({"c1": 1, "c2": 2}),
            )
        )
        fs = completed(
            model.generate(core, tc, model.ChallengeInterpretation.FIAT_SHAMIR, inv, model.ScriptedStrategy({}))
        )
        entries = list(fs.entries)
        entries[1] = replace(
            entries[1],
            draw_namespaces=(entries[0].draw_namespaces[0],),
            sampling_attempts=1,
        )
        mutated = model.mutate_record(fs, entries=tuple(entries))
        with self.assertRaisesRegex(model.ReplayError, "namespaces"):
            model.check_fresh_fs_pair(core, tc, inv, fresh, mutated)
        with self.assertRaises(model.ReplayError):
            model.replay(core, tc, inv, mutated)


class SamplingAbiTest(unittest.TestCase):
    @staticmethod
    def challenge_core() -> model.Core:
        return core_with(
            (
                model.Occurrence("c", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(129)),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            )
        )

    def find_domain(
        self, *, want_retry: bool
    ) -> tuple[model.Core, model.TranscriptConstruction, bytes]:
        core = self.challenge_core()
        for suffix in range(256):
            tc = construction(
                b"sampling-" + bytes((suffix,)),
                sample_bytes=1,
                max_attempts=8,
            )
            state = b"\x00" * 32
            sample = model.squeeze_and_sample(
                state,
                core,
                0,
                model.ChallengeDomain(129),
                tc,
            )
            if (sample.attempts > 1) == want_retry:
                return core, tc, state
        raise AssertionError("bounded search did not find the requested sampling case")

    def test_retry_advances_state_before_next_attempt(self) -> None:
        core, tc, state = self.find_domain(want_retry=True)
        sample = model.squeeze_and_sample(
            state,
            core,
            0,
            model.ChallengeDomain(129),
            tc,
        )
        first_namespace = sample.namespaces[0]
        second_namespace = sample.namespaces[1]
        first = model._squeeze_block(state, first_namespace, tc.sample_bytes)
        after_first = model._advance_state(
            state,
            first_namespace,
            tc.sample_bytes,
            first,
        )
        self.assertGreater(sample.attempts, 1)
        self.assertEqual(len(sample.namespaces), sample.attempts)
        self.assertNotEqual(first_namespace, second_namespace)
        first_namespace_datum = model.k1.decode_datum(first_namespace)
        second_namespace_datum = model.k1.decode_datum(second_namespace)
        self.assertEqual(first_namespace_datum.fields[4][1], model.k1.Nat(0))
        self.assertEqual(second_namespace_datum.fields[4][1], model.k1.Nat(1))
        self.assertNotEqual(state, after_first)
        self.assertNotEqual(sample.state, after_first)

    def test_typed_exhaustion_reports_advanced_terminal_state(self) -> None:
        core = self.challenge_core()
        found = None
        for suffix in range(256):
            tc = construction(
                b"exhaust-" + bytes((suffix,)),
                sample_bytes=1,
                max_attempts=1,
            )
            state = b"\x00" * 32
            namespace = model.derive_occurrence_namespace(core, tc, 0)
            block = model._squeeze_block(state, namespace, tc.sample_bytes)
            if block[0] >= 129:
                found = (tc, state, namespace, block)
                break
        self.assertIsNotNone(found)
        assert found is not None
        tc, state, namespace, block = found
        with self.assertRaises(model.SamplingExhausted) as raised:
            model.squeeze_and_sample(
                state,
                core,
                0,
                model.ChallengeDomain(129),
                tc,
            )
        self.assertEqual(raised.exception.attempts, 1)
        self.assertEqual(raised.exception.namespaces, (namespace,))
        self.assertEqual(
            raised.exception.terminal_state,
            model._advance_state(state, namespace, tc.sample_bytes, block),
        )

    def test_wrong_squeeze_length_refuses_before_state_advance(self) -> None:
        core, tc, _, _ = model.schnorr_fixture()
        with mock.patch.object(model, "_squeeze_block", return_value=b""):
            with self.assertRaisesRegex(model.AdmissionError, "length differs"):
                model.squeeze_and_sample(
                    model.INITIAL_TRANSCRIPT_STATE,
                    core,
                    1,
                    core.schedule[1].challenge_domain,
                    tc,
                )

    def test_same_prefix_namespace_and_domain_are_deterministic(self) -> None:
        core, tc, state = self.find_domain(want_retry=False)
        left = model.squeeze_and_sample(
            state,
            core,
            0,
            model.ChallengeDomain(129),
            tc,
        )
        right = model.squeeze_and_sample(
            state,
            core,
            0,
            model.ChallengeDomain(129),
            tc,
        )
        self.assertEqual(left, right)

    def test_domain_larger_than_word_is_refused(self) -> None:
        tc = construction(b"too-wide", sample_bytes=1)
        core = core_with(
            (
                model.Occurrence(
                    "c",
                    model.OccurrenceKind.CHALLENGE,
                    challenge_domain=model.ChallengeDomain(257),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            )
        )
        with self.assertRaisesRegex(model.AdmissionError, "sample word"):
            model.squeeze_and_sample(
                b"\x00" * 32,
                core,
                0,
                model.ChallengeDomain(257),
                tc,
            )


class NativeOracleTest(unittest.TestCase):
    def setUp(self) -> None:
        self.core, self.construction, self.invocation, self.strategy = model.oracle_fixture()

    def test_native_oracle_fresh_and_fs_lifecycle_accepts(self) -> None:
        records = []
        for interpretation in model.ChallengeInterpretation:
            record = completed(
                model.generate(
                    self.core,
                    self.construction,
                    interpretation,
                    self.invocation,
                    self.strategy,
                    fresh_resolver=(
                        model.ScriptedFreshResolver(
                            {"query_coin": 2, "fold_coin": 3}
                        )
                        if interpretation is model.ChallengeInterpretation.FRESH
                        else None
                    ),
                )
            )
            self.assertIs(record.entries[-1].value, True)
            self.assertEqual(
                model.replay(self.core, self.construction, self.invocation, record),
                record,
            )
            records.append(record)
        evidence = model.check_fresh_fs_pair(
            self.core,
            self.construction,
            self.invocation,
            *records,
        )
        self.assertTrue(evidence.fresh_terminal and evidence.fiat_shamir_terminal)

    def test_query_index_and_answer_are_derived_from_immutable_oracle(self) -> None:
        record = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                self.strategy,
                fresh_resolver=model.ScriptedFreshResolver(
                    {"query_coin": 2, "fold_coin": 3}
                ),
            )
        )
        self.assertEqual(record.entries[2].value, 2)
        self.assertEqual(record.entries[3].value, b"statement")
        oracle = record.entries[0].value
        self.assertIs(type(oracle), model.OracleObject)
        assert type(oracle) is model.OracleObject
        with self.assertRaises(FrozenInstanceError):
            oracle.cells = (b"mutated",)  # type: ignore[misc]

    def test_publication_and_answer_are_required_before_later_challenges(self) -> None:
        record = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                self.invocation,
                self.strategy,
            )
        )
        tags = tuple(frame.tag for frame in record.transcript_frames)
        self.assertLess(tags.index("oracle-publish"), tags.index("oracle-query"))
        self.assertLess(tags.index("oracle-query"), tags.index("oracle-answer"))
        query_at = tags.index("oracle-query")
        missing_query = (
            record.transcript_frames[:query_at]
            + record.transcript_frames[query_at + 1 :]
        )
        with self.assertRaises(model.ReplayError):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(record, frames=missing_query),
            )
        answer_at = tags.index("oracle-answer")
        frames = record.transcript_frames[:answer_at] + record.transcript_frames[answer_at + 1 :]
        with self.assertRaises(model.ReplayError):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(record, frames=frames),
            )

    def test_wrong_recorded_oracle_answer_is_rejected(self) -> None:
        record = completed(
            model.generate(
                self.core,
                self.construction,
                model.ChallengeInterpretation.FRESH,
                self.invocation,
                self.strategy,
                fresh_resolver=model.ScriptedFreshResolver(
                    {"query_coin": 2, "fold_coin": 3}
                ),
            )
        )
        entries = list(record.entries)
        entries[3] = replace(entries[3], value=b"forged")
        with self.assertRaises(model.ReplayError):
            model.replay(
                self.core,
                self.construction,
                self.invocation,
                model.mutate_record(record, entries=tuple(entries)),
            )

    def test_query_before_publication_is_rejected(self) -> None:
        bad = model.Core(
            inputs=(
                model.InputDecl(
                    "index",
                    model.InputRole.PUBLIC_CONTEXT,
                    value_sort=model.ValueSort.NAT,
                ),
            ),
            scopes=(model.ScopeDecl("root", None, None),),
            schedule=(
                model.Occurrence(
                    "query",
                    model.OccurrenceKind.ORACLE_QUERY,
                    dependencies=(model.ValueRef.input("index"),),
                    oracle_name="f",
                ),
                model.Occurrence("oracle", model.OccurrenceKind.ORACLE_PUBLISH, oracle_name="f"),
                model.Occurrence(
                    "answer",
                    model.OccurrenceKind.ORACLE_ANSWER,
                    dependencies=(model.ValueRef.occurrence("query"),),
                    oracle_name="f",
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            extensions=("native-oracle-v0",),
            initial_claims=("claim",),
            claim_uses=(model.ClaimConsumerUse("claim", "terminal"),),
        )
        with self.assertRaisesRegex(model.AdmissionError, "follow publication"):
            model.admit_core(bad)

    def test_query_without_answer_is_rejected(self) -> None:
        schedule = tuple(item for item in self.core.schedule if item.name != "answer")
        # Remove the dependent check and close the claims at terminal so the
        # oracle lifecycle refusal is the first relevant condition.
        schedule = tuple(item for item in schedule if item.name != "answer_nonempty")
        bad = model.Core(
            inputs=self.core.inputs,
            scopes=self.core.scopes,
            schedule=schedule,
            extensions=self.core.extensions,
            initial_claims=("claim",),
            claim_uses=(model.ClaimConsumerUse("claim", "terminal"),),
        )
        with self.assertRaisesRegex(model.AdmissionError, "every native oracle query"):
            model.admit_core(bad)

    def test_oracle_query_rejects_non_nat_index_sort(self) -> None:
        bad = core_with(
            (
                model.Occurrence(
                    "oracle",
                    model.OccurrenceKind.ORACLE_PUBLISH,
                    oracle_name="f",
                ),
                model.Occurrence(
                    "query",
                    model.OccurrenceKind.ORACLE_QUERY,
                    dependencies=(model.ValueRef.input("index"),),
                    oracle_name="f",
                ),
                model.Occurrence(
                    "answer",
                    model.OccurrenceKind.ORACLE_ANSWER,
                    dependencies=(model.ValueRef.occurrence("query"),),
                    oracle_name="f",
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(model.InputDecl("index", model.InputRole.PUBLIC_CONTEXT),),
            extensions=("native-oracle-v0",),
        )
        with self.assertRaisesRegex(model.AdmissionError, "Nat sort"):
            model.admit_core(bad)

    def test_oracle_query_rejects_index_from_not_yet_open_scope(self) -> None:
        bad = core_with(
            (
                model.Occurrence(
                    "oracle",
                    model.OccurrenceKind.ORACLE_PUBLISH,
                    oracle_name="f",
                ),
                model.Occurrence(
                    "query",
                    model.OccurrenceKind.ORACLE_QUERY,
                    dependencies=(model.ValueRef.input("child-index"),),
                    oracle_name="f",
                ),
                model.Occurrence(
                    "child-marker",
                    model.OccurrenceKind.PROVER_MESSAGE,
                    scope="child",
                ),
                model.Occurrence(
                    "answer",
                    model.OccurrenceKind.ORACLE_ANSWER,
                    dependencies=(model.ValueRef.occurrence("query"),),
                    oracle_name="f",
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl(
                    "child-index",
                    model.InputRole.PUBLIC_CONTEXT,
                    "child",
                    model.ValueSort.NAT,
                ),
            ),
            scopes=(
                model.ScopeDecl("root", None, None),
                model.ScopeDecl("child", "root", "child-marker"),
            ),
            extensions=("native-oracle-v0",),
        )
        with self.assertRaisesRegex(model.AdmissionError, "exact prior prefix"):
            model.admit_core(bad)

    def test_unknown_extension_is_refused_fail_closed(self) -> None:
        bad = replace(self.core, extensions=("native-oracle-v0", "vendor-magic-v9"))
        with self.assertRaisesRegex(model.AdmissionError, "unsupported extension"):
            model.admit_core(bad)

    def test_oracle_events_require_the_standard_extension(self) -> None:
        with self.assertRaisesRegex(model.AdmissionError, "must agree"):
            model.admit_core(replace(self.core, extensions=()))


class ScheduleScopeAndClosureTest(unittest.TestCase):
    def test_schedule_order_is_identity_bearing(self) -> None:
        schedule = (
            model.Occurrence("a", model.OccurrenceKind.PROVER_MESSAGE),
            model.Occurrence("b", model.OccurrenceKind.PROVER_MESSAGE),
            model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
        )
        left = core_with(schedule)
        right = core_with((schedule[1], schedule[0], schedule[2]))
        self.assertNotEqual(model.core_id(left), model.core_id(right))

    def test_dependency_cannot_point_forward_after_reorder(self) -> None:
        bad = core_with(
            (
                model.Occurrence(
                    "use",
                    model.OccurrenceKind.VERIFIER_MESSAGE,
                    dependencies=(model.ValueRef.occurrence("future"),),
                    verifier_rule=model.VerifierRule(model.VerifierRuleKind.COPY),
                ),
                model.Occurrence("future", model.OccurrenceKind.PROVER_MESSAGE),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            )
        )
        with self.assertRaisesRegex(model.AdmissionError, "exact prior prefix"):
            model.admit_core(bad)

    def test_prover_message_rejects_authored_dependencies(self) -> None:
        bad = core_with(
            (
                model.Occurrence(
                    "message",
                    model.OccurrenceKind.PROVER_MESSAGE,
                    dependencies=(model.ValueRef.input("public"),),
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl("public", model.InputRole.PUBLIC_CONTEXT),
            ),
        )
        with self.assertRaisesRegex(model.AdmissionError, "no authored dependency"):
            model.admit_core(bad)

    def test_child_scope_statement_opens_on_continuous_state(self) -> None:
        core = core_with(
            (
                model.Occurrence("parent_message", model.OccurrenceKind.PROVER_MESSAGE),
                model.Occurrence("parent_challenge", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(11)),
                model.Occurrence("child_message", model.OccurrenceKind.PROVER_MESSAGE, scope="child"),
                model.Occurrence("child_challenge", model.OccurrenceKind.CHALLENGE, scope="child", challenge_domain=model.ChallengeDomain(13)),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl("root_statement", model.InputRole.STATEMENT, "root"),
                model.InputDecl("child_statement", model.InputRole.STATEMENT, "child"),
                model.InputDecl(
                    "child_context",
                    model.InputRole.PUBLIC_CONTEXT,
                    "child",
                ),
                model.InputDecl(
                    "child_parameter",
                    model.InputRole.PUBLIC_PARAMETER,
                    "child",
                ),
            ),
            scopes=(
                model.ScopeDecl("root", None, None),
                model.ScopeDecl("child", "root", "child_message"),
            ),
        )
        tc = construction(b"composition")
        inv = invocation(
            {
                "root_statement": b"root",
                "child_statement": b"child",
                "child_context": b"context",
                "child_parameter": b"parameter",
            }
        )
        record = completed(
            model.generate(
                core,
                tc,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                inv,
                model.ScriptedStrategy({"parent_message": b"p", "child_message": b"c"}),
            )
        )
        tags = tuple(frame.tag for frame in record.transcript_frames)
        self.assertEqual(tags.count("scope-open"), 2)
        self.assertEqual(tags.count("statement"), 2)
        child_scope = [i for i, frame in enumerate(record.transcript_frames) if frame.tag == "scope-open"][1]
        child_statement = [i for i, frame in enumerate(record.transcript_frames) if frame.tag == "statement"][1]
        self.assertLess(child_scope, child_statement)
        self.assertEqual(
            tags[child_scope + 1 : child_scope + 4],
            ("statement", "public-context", "public-parameter"),
        )
        second_prefix = next(
            item.prefix_state for item in record.entries if item.occurrence == "child_challenge"
        )
        self.assertNotEqual(second_prefix, model._initial_state())

    def test_parent_strategy_cannot_read_child_scope_input_early(self) -> None:
        core = core_with(
            (
                model.Occurrence(
                    "parent_message",
                    model.OccurrenceKind.PROVER_MESSAGE,
                ),
                model.Occurrence(
                    "child_message",
                    model.OccurrenceKind.PROVER_MESSAGE,
                    scope="child",
                ),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(
                model.InputDecl(
                    "child_statement",
                    model.InputRole.STATEMENT,
                    "child",
                ),
            ),
            scopes=(
                model.ScopeDecl("root", None, None),
                model.ScopeDecl("child", "root", "child_message"),
            ),
        )

        class EarlyReader:
            def move(
                self,
                occurrence: model.Occurrence,
                view: model.ProverView,
            ) -> model.Value:
                if occurrence.name == "parent_message":
                    return view.public_input("child_statement")
                return b"child"

        result = model.generate(
            core,
            construction(b"scope-visibility"),
            model.ChallengeInterpretation.FIAT_SHAMIR,
            invocation({"child_statement": b"statement"}),
            EarlyReader(),
        )
        self.assertIs(type(result), model.Noncompletion)
        assert type(result) is model.Noncompletion
        self.assertIs(result.reason, model.NoncompletionReason.FUTURE_READ)

    def test_missing_child_statement_frame_is_rejected(self) -> None:
        core = core_with(
            (
                model.Occurrence("child_message", model.OccurrenceKind.PROVER_MESSAGE, scope="child"),
                model.Occurrence("challenge", model.OccurrenceKind.CHALLENGE, scope="child", challenge_domain=model.ChallengeDomain(7)),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            inputs=(model.InputDecl("statement", model.InputRole.STATEMENT, "child"),),
            scopes=(
                model.ScopeDecl("root", None, None),
                model.ScopeDecl("child", "root", "child_message"),
            ),
        )
        tc = construction(b"child-statement")
        inv = invocation({"statement": b"child"})
        record = completed(
            model.generate(
                core,
                tc,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                inv,
                model.ScriptedStrategy({"child_message": b"proof"}),
            )
        )
        statement = next(i for i, frame in enumerate(record.transcript_frames) if frame.tag == "statement")
        frames = record.transcript_frames[:statement] + record.transcript_frames[statement + 1 :]
        with self.assertRaises(model.ReplayError):
            model.replay(core, tc, inv, model.mutate_record(record, frames=frames))

    def test_claim_use_is_linear(self) -> None:
        core = core_with(
            (
                model.Occurrence("a", model.OccurrenceKind.PROVER_MESSAGE),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            )
        )
        bad = replace(
            core,
            initial_claims=("claim",),
            reductions=(
                model.ReductionDecl(
                    "r",
                    "a",
                    "root",
                    ("claim",),
                    (),
                    (),
                    (),
                    ("next",),
                ),
            ),
            claim_uses=(
                model.ClaimConsumerUse("claim", "r"),
                model.ClaimConsumerUse("claim", "terminal"),
            ),
        )
        with self.assertRaisesRegex(model.AdmissionError, "linear"):
            model.admit_core(bad)

    def test_reduction_required_publication_cannot_follow_its_challenge(self) -> None:
        core = model.Core(
            inputs=(),
            scopes=(model.ScopeDecl("root", None, None),),
            schedule=(
                model.Occurrence("c", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(7)),
                model.Occurrence("late", model.OccurrenceKind.PROVER_MESSAGE),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            ),
            initial_claims=("claim",),
            reductions=(
                model.ReductionDecl(
                    "late-reduction",
                    "terminal",
                    "root",
                    ("claim",),
                    (),
                    ("c",),
                    (model.RequiredPublication("late", "c"),),
                    ("final",),
                ),
            ),
            claim_uses=(
                model.ClaimConsumerUse("claim", "late-reduction"),
                model.ClaimConsumerUse("final", "terminal"),
            ),
        )
        with self.assertRaisesRegex(model.AdmissionError, "least following challenge"):
            model.admit_core(core)

    def test_reduction_side_input_publication_closure_is_complete(self) -> None:
        core, _, _, _ = model.schnorr_fixture()
        reduction = core.reductions[0]
        bad = replace(
            core,
            reductions=(
                replace(
                    reduction,
                    required_publications=(reduction.required_publications[0],),
                ),
            ),
        )
        with self.assertRaisesRegex(model.AdmissionError, "closure is incomplete"):
            model.admit_core(bad)

    def test_terminal_closure_is_exact(self) -> None:
        no_terminal = model.Core(
            inputs=(),
            scopes=(model.ScopeDecl("root", None, None),),
            schedule=(model.Occurrence("message", model.OccurrenceKind.PROVER_MESSAGE),),
            initial_claims=("claim",),
            claim_uses=(model.ClaimConsumerUse("claim", "message"),),
        )
        with self.assertRaisesRegex(model.AdmissionError, "exactly one terminal"):
            model.admit_core(no_terminal)
        live_claim = core_with((model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),))
        bad = replace(
            live_claim,
            initial_claims=("a", "b"),
            claim_uses=(model.ClaimConsumerUse("a", "terminal"),),
        )
        with self.assertRaisesRegex(model.AdmissionError, "consume every"):
            model.admit_core(bad)


class GrindingSeparationTest(unittest.TestCase):
    def test_grinding_is_an_explicit_prover_message_and_check(self) -> None:
        dependencies = (model.ValueRef.occurrence("nonce"),)
        core = core_with(
            (
                model.Occurrence("nonce", model.OccurrenceKind.PROVER_MESSAGE),
                model.Occurrence(
                    "pow_check",
                    model.OccurrenceKind.CHECK,
                    dependencies=dependencies,
                    check_predicate=model.Predicate(
                        model.PredicateKind.LEADING_ZERO_BITS,
                        dependencies,
                        (4,),
                    ),
                ),
                model.Occurrence("challenge", model.OccurrenceKind.CHALLENGE, challenge_domain=model.ChallengeDomain(11)),
                model.Occurrence("terminal", model.OccurrenceKind.TERMINAL),
            )
        )
        nonce = next(
            value.to_bytes(4, "big")
            for value in range(1 << 16)
            if int.from_bytes(hashlib.sha256(value.to_bytes(4, "big")).digest(), "big") < (1 << 252)
        )
        tc = construction(b"grinding")
        record = completed(
            model.generate(
                core,
                tc,
                model.ChallengeInterpretation.FIAT_SHAMIR,
                invocation({}),
                model.ScriptedStrategy({"nonce": nonce}),
            )
        )
        self.assertIs(record.entries[1].value, True)
        self.assertIn("prover-message", tuple(frame.tag for frame in record.transcript_frames))
        challenge = record.entries[2]
        self.assertGreaterEqual(challenge.sampling_attempts or 0, 1)
        self.assertFalse(hasattr(tc, "grinding_bits"))


if __name__ == "__main__":
    unittest.main()
