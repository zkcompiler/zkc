"""Tests for the exact typed FRI Fiat--Shamir transcript construction."""

from __future__ import annotations

from dataclasses import replace
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from friiormodel.commitment import EXACT_COMMITMENT_PROFILE, MerkleCap  # noqa: E402
from friiormodel.field import Fp, Fp2, MODULUS  # noqa: E402
from friiormodel.profile import EXACT_ALGEBRA_PROFILE, EXACT_PROFILE  # noqa: E402
import friiormodel.transcript as transcript_model  # noqa: E402
from friiormodel.terms import (  # noqa: E402
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
    ResourceLimits,
    encode_term,
    semantic_id,
)
from friiormodel.transcript import (  # noqa: E402
    APPLICATION_CONTEXT_NAMESPACE,
    BETA0,
    BETA0_NAMESPACE,
    BETA1_NAMESPACE,
    CANONICAL_CONSTRUCTION_PLAN,
    CAP0,
    CAP0_NAMESPACE,
    CAP1,
    CAP1_NAMESPACE,
    CAP_CODEC,
    CLOSED_TERM_CODEC,
    EXACT_GRINDING_PROFILE,
    EXACT_TRANSCRIPT_LAWS,
    FP2_SAMPLER,
    GRINDING_BITS,
    GRINDING_NONCE,
    GRINDING_NONCE_NAMESPACE,
    MAX_GRINDING_NONCE,
    MODEL,
    NONCE_CODEC,
    QUERY_OCCURRENCES_NAMESPACE,
    QUERY_SAMPLER,
    QUERY_SEED,
    QUERY_SEED_NAMESPACE,
    SEED_SAMPLER,
    STATEMENT,
    STATEMENT_NAMESPACE,
    TERMINAL,
    TERMINAL_CODEC,
    TERMINAL_NAMESPACE,
    WORK_SEED_NAMESPACE,
    GrindingProfile,
    FiatShamirTranscript,
    admit_construction_plan,
    construct_fiat_shamir_transcript,
    derive_fiat_shamir_transcript,
)


GENESIS_DOMAIN = b"zkc.fri-ior.transcript-genesis.v1\x00"
ABSORB_DOMAIN = b"zkc.fri-ior.transcript-absorb.v1\x00"
SQUEEZE_DOMAIN = b"zkc.fri-ior.transcript-squeeze.v1\x00"
QUERY_EXPAND_DOMAIN = b"zkc.fri-ior.query-expand.v1\x00"
WORK_DOMAIN = b"zkc.fri-ior.work-check.v1\x00"


def _cap(label: str) -> MerkleCap:
    return MerkleCap(
        (
            hashlib.sha256(f"{label}-left".encode("ascii")).digest(),
            hashlib.sha256(f"{label}-right".encode("ascii")).digest(),
        )
    )


STATEMENT_TERM = {
    "relation": "rs-proximity",
    "domain": "D0",
    "degree_bound_exclusive": 8,
}
APPLICATION_CONTEXT_TERM = {
    "application": "zkc-native-fri-ior-evaluation",
    "version": 1,
    "fixture_selector": 9,
}
CAP0_VALUE = _cap("cap0")
CAP1_VALUE = _cap("cap1")
TERMINAL_COEFFICIENTS = (
    Fp2(Fp(7), Fp(11)),
    Fp2(Fp(13), Fp(17)),
)


def _replace_step(occurrence: str, **changes: object):
    steps = tuple(
        replace(step, **changes) if step.occurrence == occurrence else step
        for step in CANONICAL_CONSTRUCTION_PLAN.steps
    )
    return replace(CANONICAL_CONSTRUCTION_PLAN, steps=steps)


def _move_before(moving: str, target: str):
    steps = list(CANONICAL_CONSTRUCTION_PLAN.steps)
    selected = next(step for step in steps if step.occurrence == moving)
    steps.remove(selected)
    target_index = next(
        index for index, step in enumerate(steps) if step.occurrence == target
    )
    steps.insert(target_index, selected)
    return replace(CANONICAL_CONSTRUCTION_PLAN, steps=tuple(steps))


def _reference_frame(namespace: str, codec: str, payload: bytes) -> bytes:
    namespace_bytes = namespace.encode("ascii")
    codec_bytes = codec.encode("ascii")
    return (
        len(namespace_bytes).to_bytes(2, "big")
        + namespace_bytes
        + len(codec_bytes).to_bytes(2, "big")
        + codec_bytes
        + len(payload).to_bytes(4, "big")
        + payload
    )


def _reference_hash(payload: bytes) -> bytes:
    return hashlib.sha256(payload).digest()


def _reference_absorb(
    state: bytes,
    namespace: str,
    codec: str,
    payload: bytes,
) -> bytes:
    return _reference_hash(
        ABSORB_DOMAIN + state + _reference_frame(namespace, codec, payload)
    )


def _reference_squeeze(
    state: bytes,
    namespace: str,
    sampler: str,
    attempt: int,
) -> bytes:
    return _reference_hash(
        SQUEEZE_DOMAIN
        + state
        + _reference_frame(namespace, sampler, attempt.to_bytes(2, "big"))
    )


def _reference_fp2(state: bytes, namespace: str) -> tuple[Fp2, bytes]:
    cardinality = MODULUS * MODULUS
    ceiling = ((1 << 16) // cardinality) * cardinality
    for attempt in range(64):
        digest = _reference_squeeze(state, namespace, FP2_SAMPLER, attempt)
        candidate = int.from_bytes(digest[:2], "big")
        if candidate < ceiling:
            residue = candidate % cardinality
            return Fp2(Fp(residue // MODULUS), Fp(residue % MODULUS)), digest
    raise AssertionError("reference Fp2 sampler exhausted its exact syntax bound")


def _reference_work_digest(work_seed: bytes, nonce: int) -> bytes:
    return _reference_hash(
        WORK_DOMAIN
        + _reference_frame(
            "zkc/fri-ior/work-check/v1",
            "sha256-leading-zero-bits.v1",
            work_seed + nonce.to_bytes(4, "big"),
        )
    )


def _reference_reconstruction(nonce: int) -> dict[str, object]:
    plan = CANONICAL_CONSTRUCTION_PLAN
    state = _reference_hash(
        GENESIS_DOMAIN
        + encode_term(
            {
                "model": MODEL,
                "algebra_profile_id": plan.algebra_profile_id.to_term(),
                "commitment_profile_id": plan.commitment_profile_id.to_term(),
                "grinding_profile_id": plan.grinding_profile_id.to_term(),
                "transcript_semantic_law_ids": [
                    identity.to_term() for identity in plan.semantic_law_ids
                ],
            }
        )
    )
    state = _reference_absorb(
        state,
        STATEMENT_NAMESPACE,
        CLOSED_TERM_CODEC,
        encode_term(STATEMENT_TERM),
    )
    state = _reference_absorb(
        state,
        APPLICATION_CONTEXT_NAMESPACE,
        CLOSED_TERM_CODEC,
        encode_term(APPLICATION_CONTEXT_TERM),
    )
    state = _reference_absorb(
        state,
        CAP0_NAMESPACE,
        CAP_CODEC,
        encode_term(CAP0_VALUE.to_term()),
    )
    beta0, state = _reference_fp2(state, BETA0_NAMESPACE)
    state = _reference_absorb(
        state,
        CAP1_NAMESPACE,
        CAP_CODEC,
        encode_term(CAP1_VALUE.to_term()),
    )
    beta1, state = _reference_fp2(state, BETA1_NAMESPACE)
    terminal_payload = encode_term(
        {
            "coefficient_order": "ascending",
            "coefficients": [item.to_term() for item in TERMINAL_COEFFICIENTS],
        }
    )
    state = _reference_absorb(
        state,
        TERMINAL_NAMESPACE,
        TERMINAL_CODEC,
        terminal_payload,
    )
    work_seed = _reference_squeeze(state, WORK_SEED_NAMESPACE, SEED_SAMPLER, 0)
    state = _reference_absorb(
        work_seed,
        GRINDING_NONCE_NAMESPACE,
        NONCE_CODEC,
        nonce.to_bytes(4, "big"),
    )
    work_digest = _reference_work_digest(work_seed, nonce)
    if work_digest[0] >> (8 - GRINDING_BITS) != 0:
        raise AssertionError("the fixed reference nonce does not satisfy work")
    query_seed = _reference_squeeze(state, QUERY_SEED_NAMESPACE, SEED_SAMPLER, 0)
    query_indices: list[int] = []
    query_domain_size = plan.query_domain_size
    if query_domain_size & (query_domain_size - 1) != 0:
        raise AssertionError("the fixed query domain is not a power of two")
    index_mask = query_domain_size - 1
    for ordinal in range(plan.query_count):
        digest = _reference_hash(
            QUERY_EXPAND_DOMAIN
            + query_seed
            + _reference_frame(
                QUERY_OCCURRENCES_NAMESPACE,
                QUERY_SAMPLER,
                ordinal.to_bytes(2, "big"),
            )
        )
        candidate = int.from_bytes(digest[:2], "big")
        query_indices.append(candidate & index_mask)
    return {
        "beta0": beta0,
        "beta1": beta1,
        "work_seed": work_seed,
        "work_digest": work_digest,
        "query_seed": query_seed,
        "query_indices": tuple(query_indices),
    }


def _derive_fixture(
    *,
    statement: object = STATEMENT_TERM,
    application_context: object = APPLICATION_CONTEXT_TERM,
    cap0: MerkleCap = CAP0_VALUE,
    cap1: MerkleCap = CAP1_VALUE,
    terminal: tuple[Fp2, ...] = TERMINAL_COEFFICIENTS,
    resources: ResourceCounter | None = None,
) -> FiatShamirTranscript:
    completed = construct_fiat_shamir_transcript(
        CANONICAL_CONSTRUCTION_PLAN,
        statement,
        application_context,
        cap0,
        cap1,
        terminal,
        resources,
    )
    if isinstance(completed, CheckResult):
        raise AssertionError(completed)
    return completed


def _request_limits(
    *,
    hash_calls: int,
    hash_bytes: int,
    sampler_attempts: int = 128,
    grinding_trials: int = 128,
) -> ResourceLimits:
    return ResourceLimits(
        field_operations=0,
        hash_calls=hash_calls,
        hash_bytes=hash_bytes,
        merkle_nodes=0,
        transcript_frames=128,
        sampler_attempts=sampler_attempts,
        grinding_trials=grinding_trials,
        logical_query_occurrences=16,
        unique_openings=0,
        proof_bytes=0,
    )


class ConstructionPlanAdmissionTest(unittest.TestCase):
    def test_exact_plan_is_admitted(self) -> None:
        result = admit_construction_plan(CANONICAL_CONSTRUCTION_PLAN)
        self.assertIs(result.outcome, OutcomeClass.AFFIRMATIVE)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-100")
        self.assertEqual(result.subject, CANONICAL_CONSTRUCTION_PLAN.identity)

    def test_non_plan_input_is_malformed(self) -> None:
        result = admit_construction_plan({"model": MODEL})
        self.assertIs(result.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-001")

    def test_well_formed_alternate_hash_law_is_unsupported(self) -> None:
        alternate_hash_law_id = semantic_id(
            "fri-ior-semantic-law",
            "fri-ior.semantic-law.v1",
            {"name": "alternate-sha512-transcript-law"},
        )
        alternate = replace(
            CANONICAL_CONSTRUCTION_PLAN,
            semantic_law_ids=(
                alternate_hash_law_id,
                *CANONICAL_CONSTRUCTION_PLAN.semantic_law_ids[1:],
            ),
        )
        result = admit_construction_plan(alternate)
        self.assertIs(result.outcome, OutcomeClass.UNSUPPORTED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-019")

    def test_missing_statement_cap_or_terminal_is_refused(self) -> None:
        for occurrence in (STATEMENT, CAP0, CAP1, TERMINAL):
            with self.subTest(occurrence=occurrence):
                plan = replace(
                    CANONICAL_CONSTRUCTION_PLAN,
                    steps=tuple(
                        step
                        for step in CANONICAL_CONSTRUCTION_PLAN.steps
                        if step.occurrence != occurrence
                    ),
                )
                result = admit_construction_plan(plan)
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-010")

    def test_cap_after_its_challenge_is_refused_as_reordered(self) -> None:
        plan = _move_before(BETA0, CAP0)
        result = admit_construction_plan(plan)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-011")

    def test_unprotected_statement_is_refused(self) -> None:
        statement_step = next(
            step
            for step in CANONICAL_CONSTRUCTION_PLAN.steps
            if step.occurrence == STATEMENT
        )
        plan = _replace_step(
            STATEMENT,
            protected_occurrences=statement_step.protected_occurrences[1:],
        )
        result = admit_construction_plan(plan)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-012")

    def test_message_excluded_from_influence_is_refused(self) -> None:
        plan = _replace_step(CAP1, feeds_transcript_state=False)
        result = admit_construction_plan(plan)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-016")

    def test_wrong_namespace_codec_and_sampler_have_distinct_boundaries(self) -> None:
        mutations = (
            (
                _replace_step(CAP0, namespace="zkc/fri-ior/wrong/v1"),
                "FRI-IOR-TRANSCRIPT-013",
            ),
            (
                _replace_step(CAP0, codec="raw-digest-concatenation.v1"),
                "FRI-IOR-TRANSCRIPT-014",
            ),
            (
                _replace_step(BETA0, sampler="sha256-modulo-biased.v1"),
                "FRI-IOR-TRANSCRIPT-015",
            ),
        )
        for plan, code in mutations:
            with self.subTest(code=code):
                result = admit_construction_plan(plan)
                self.assertIs(result.outcome, OutcomeClass.REFUSED)
                self.assertEqual(result.code, code)

    def test_query_randomness_before_terminal_is_refused_first(self) -> None:
        plan = _move_before(QUERY_SEED, TERMINAL)
        result = admit_construction_plan(plan)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-017")

    def test_grinding_after_query_randomness_is_refused(self) -> None:
        plan = _move_before(QUERY_SEED, GRINDING_NONCE)
        result = admit_construction_plan(plan)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-018")

    def test_attempt_bounds_are_resource_inputs_not_plan_semantics(self) -> None:
        plan_identity = CANONICAL_CONSTRUCTION_PLAN.identity
        plan_term = CANONICAL_CONSTRUCTION_PLAN.to_term()
        first = ResourceCounter(
            _request_limits(
                hash_calls=32,
                hash_bytes=1 << 14,
                sampler_attempts=8,
                grinding_trials=16,
            )
        )
        second = ResourceCounter(
            _request_limits(
                hash_calls=64,
                hash_bytes=1 << 15,
                sampler_attempts=32,
                grinding_trials=64,
            )
        )
        self.assertNotEqual(first.limits, second.limits)
        self.assertFalse(
            hasattr(CANONICAL_CONSTRUCTION_PLAN, "rejection_attempt_bound")
        )
        self.assertFalse(
            hasattr(CANONICAL_CONSTRUCTION_PLAN, "grinding_search_attempt_bound")
        )
        self.assertIs(
            admit_construction_plan(CANONICAL_CONSTRUCTION_PLAN).outcome,
            OutcomeClass.AFFIRMATIVE,
        )
        self.assertNotIn("resources", plan_term)
        self.assertNotIn("resource_limits", plan_term)
        self.assertNotIn("rejection_attempt_bound", plan_term)
        self.assertNotIn("grinding_search_attempt_bound", plan_term)
        self.assertEqual(CANONICAL_CONSTRUCTION_PLAN.identity, plan_identity)

    def test_plan_identity_changes_with_plan_semantics(self) -> None:
        alternate_grinding = replace(EXACT_GRINDING_PROFILE, difficulty_bits=3)
        alternate = replace(
            CANONICAL_CONSTRUCTION_PLAN,
            grinding_profile_id=alternate_grinding.identity,
        )
        self.assertNotEqual(
            alternate.identity,
            CANONICAL_CONSTRUCTION_PLAN.identity,
        )
        self.assertEqual(
            CANONICAL_CONSTRUCTION_PLAN.identity.subject_kind,
            "transcript-construction-plan",
        )
        self.assertEqual(
            CANONICAL_CONSTRUCTION_PLAN.identity.domain,
            "fri-ior.transcript-construction-plan.v1",
        )

    def test_plan_selects_exact_factored_dependencies_and_laws(self) -> None:
        plan = CANONICAL_CONSTRUCTION_PLAN
        self.assertIsInstance(EXACT_GRINDING_PROFILE, GrindingProfile)
        self.assertEqual(plan.algebra_profile_id, EXACT_ALGEBRA_PROFILE.identity)
        self.assertEqual(
            plan.commitment_profile_id,
            EXACT_COMMITMENT_PROFILE.identity,
        )
        self.assertEqual(plan.grinding_profile_id, EXACT_GRINDING_PROFILE.identity)
        self.assertEqual(
            plan.semantic_law_ids,
            tuple(law.identity for law in EXACT_TRANSCRIPT_LAWS),
        )
        term = plan.to_term()
        self.assertEqual(len(term["semantic_law_ids"]), len(EXACT_TRANSCRIPT_LAWS))


class TranscriptDerivationTest(unittest.TestCase):
    def test_exact_vector_and_separately_coded_transition_reconstruction(self) -> None:
        counter = ResourceCounter()
        transcript = _derive_fixture(resources=counter)
        reference = _reference_reconstruction(transcript.grinding_nonce)

        self.assertEqual(transcript.beta0.to_term(), [12, 17])
        self.assertEqual(transcript.beta1.to_term(), [63, 39])
        self.assertEqual(transcript.grinding_nonce, 4)
        self.assertEqual(
            transcript.work_seed.hex(),
            "57ad0e6ee70074e132c23f4f7a5600707889f9940fb8a5b75afa104c684da4a6",
        )
        self.assertEqual(
            transcript.work_digest.hex(),
            "1f9a80d52c43dbd4812f02a749f887e58285f560efd6c157135be903573a1c60",
        )
        self.assertEqual(
            transcript.query_seed.hex(),
            "fb19906929b63dc3cdd2abde07198000ae2995edb10f9a889f93a3e4c1bbba76",
        )
        self.assertEqual(
            tuple(item.initial_domain_index for item in transcript.query_occurrences),
            (10, 8, 2, 5),
        )
        self.assertEqual(transcript.beta0, reference["beta0"])
        self.assertEqual(transcript.beta1, reference["beta1"])
        self.assertEqual(transcript.work_seed, reference["work_seed"])
        self.assertEqual(transcript.work_digest, reference["work_digest"])
        self.assertEqual(transcript.query_seed, reference["query_seed"])
        self.assertEqual(
            tuple(item.initial_domain_index for item in transcript.query_occurrences),
            reference["query_indices"],
        )
        self.assertEqual(counter.snapshot()["hash_calls"], 23)
        self.assertEqual(counter.snapshot()["transcript_frames"], 22)
        self.assertEqual(counter.snapshot()["sampler_attempts"], 10)
        self.assertEqual(counter.snapshot()["grinding_trials"], 6)
        self.assertEqual(counter.snapshot()["logical_query_occurrences"], 0)

    def test_equal_query_values_keep_distinct_ordinals(self) -> None:
        occurrences = _derive_fixture(
            statement={**STATEMENT_TERM, "variant": 4}
        ).query_occurrences
        self.assertEqual(
            tuple(item.ordinal for item in occurrences),
            (0, 1, 2, 3),
        )
        self.assertEqual(occurrences[1].initial_domain_index, 8)
        self.assertEqual(occurrences[2].initial_domain_index, 8)
        self.assertNotEqual(
            occurrences[1].ordinal,
            occurrences[2].ordinal,
        )

    def test_opposite_initial_points_are_not_collapsed_during_sampling(self) -> None:
        occurrences = _derive_fixture(
            statement={**STATEMENT_TERM, "variant": 1}
        ).query_occurrences
        first = occurrences[1].initial_domain_index
        opposite = occurrences[2].initial_domain_index
        self.assertEqual((first, opposite), (5, 13))
        self.assertNotEqual(first, opposite)
        pair_count = EXACT_PROFILE.domains[0].order // 2
        self.assertEqual(first % pair_count, opposite % pair_count)
        indices = tuple(item.initial_domain_index for item in occurrences)
        layer0_pairs = {index % 8 for index in indices}
        layer1_pairs = {index % 4 for index in indices}
        self.assertGreaterEqual(len(layer0_pairs), 2)
        self.assertLess(
            len(layer0_pairs) + len(layer1_pairs),
            2 * len(occurrences),
        )

    def test_each_public_prefix_source_influences_its_next_coin(self) -> None:
        transcript = _derive_fixture()
        changed_statement = _derive_fixture(
            statement={**STATEMENT_TERM, "degree_bound_exclusive": 7}
        )
        changed_context = _derive_fixture(
            application_context={**APPLICATION_CONTEXT_TERM, "version": 2}
        )
        changed_cap0 = _derive_fixture(cap0=_cap("other-cap0"))
        changed_cap1 = _derive_fixture(cap1=_cap("other-cap1"))
        changed_terminal = _derive_fixture(
            terminal=(Fp2(Fp(19), Fp(23)), Fp2(Fp(29), Fp(31)))
        )

        self.assertNotEqual(transcript.beta0, changed_statement.beta0)
        self.assertNotEqual(transcript.beta0, changed_context.beta0)
        self.assertNotEqual(transcript.beta0, changed_cap0.beta0)
        self.assertEqual(transcript.beta0, changed_cap1.beta0)
        self.assertNotEqual(transcript.beta1, changed_cap1.beta1)
        self.assertEqual(transcript.beta0, changed_terminal.beta0)
        self.assertEqual(transcript.beta1, changed_terminal.beta1)
        self.assertNotEqual(transcript.work_seed, changed_terminal.work_seed)

    def test_work_seed_and_query_seed_are_distinct_challenge_domains(self) -> None:
        transcript = _derive_fixture()
        self.assertNotEqual(transcript.work_seed, transcript.query_seed)

    def test_invalid_grinding_nonce_refuses_before_query_derivation(self) -> None:
        transcript = _derive_fixture()
        failing_nonce = next(
            nonce
            for nonce in range(16)
            if nonce != transcript.grinding_nonce
            and _reference_work_digest(transcript.work_seed, nonce)[0]
            >> (8 - GRINDING_BITS)
            != 0
        )
        counter = ResourceCounter()
        result = derive_fiat_shamir_transcript(
            CANONICAL_CONSTRUCTION_PLAN,
            STATEMENT_TERM,
            APPLICATION_CONTEXT_TERM,
            CAP0_VALUE,
            CAP1_VALUE,
            TERMINAL_COEFFICIENTS,
            failing_nonce,
            counter,
        )
        self.assertIsInstance(result, CheckResult)
        assert isinstance(result, CheckResult)
        self.assertIs(result.outcome, OutcomeClass.REFUSED)
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-037")
        self.assertEqual(counter.hash_calls, 13)
        self.assertEqual(counter.transcript_frames, 12)
        self.assertEqual(counter.grinding_trials, 1)
        self.assertEqual(counter.sampler_attempts, 5)

    def test_non_u32_nonce_is_malformed(self) -> None:
        for nonce in (-1, MAX_GRINDING_NONCE + 1, True, "4"):
            with self.subTest(nonce=nonce):
                result = derive_fiat_shamir_transcript(
                    CANONICAL_CONSTRUCTION_PLAN,
                    STATEMENT_TERM,
                    APPLICATION_CONTEXT_TERM,
                    CAP0_VALUE,
                    CAP1_VALUE,
                    TERMINAL_COEFFICIENTS,
                    nonce,
                )
                self.assertIsInstance(result, CheckResult)
                assert isinstance(result, CheckResult)
                self.assertIs(result.outcome, OutcomeClass.MALFORMED)
                self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-024")

    def test_one_counter_threads_across_every_transcript_phase(self) -> None:
        counter = ResourceCounter(
            ResourceLimits(
                field_operations=0,
                hash_calls=8,
                hash_bytes=1 << 15,
                merkle_nodes=0,
                transcript_frames=32,
                sampler_attempts=32,
                grinding_trials=32,
                logical_query_occurrences=8,
                unique_openings=0,
                proof_bytes=0,
            )
        )
        result = derive_fiat_shamir_transcript(
            CANONICAL_CONSTRUCTION_PLAN,
            STATEMENT_TERM,
            APPLICATION_CONTEXT_TERM,
            CAP0_VALUE,
            CAP1_VALUE,
            TERMINAL_COEFFICIENTS,
            6,
            counter,
        )
        self.assertIsInstance(result, CheckResult)
        assert isinstance(result, CheckResult)
        self.assertIs(
            result.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(result.code, "FRI-IOR-RESOURCE-008")
        self.assertEqual(counter.hash_calls, 8)

    def test_internal_stage_carriers_validate_shape_but_are_not_public_inputs(
        self,
    ) -> None:
        with self.assertRaises(ModelFailure) as raised:
            transcript_model._FirstRoundTranscript(  # noqa: SLF001
                CANONICAL_CONSTRUCTION_PLAN,
                b"short",
                Fp2.zero(),
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-TRANSCRIPT-039")

        transcript = _derive_fixture()
        with self.assertRaises(ModelFailure) as raised:
            replace(
                transcript,
                query_occurrences=transcript.query_occurrences[:-1],
            )
        self.assertIs(raised.exception.outcome, OutcomeClass.MALFORMED)
        self.assertEqual(raised.exception.code, "FRI-IOR-TRANSCRIPT-047")


class ResourceBoundDiagnosticsTest(unittest.TestCase):
    def test_fp2_sampler_exhausts_the_selected_resource_budget(self) -> None:
        resources = ResourceCounter(
            _request_limits(
                hash_calls=32,
                hash_bytes=1 << 14,
                sampler_attempts=3,
                grinding_trials=16,
            )
        )
        with patch.object(
            transcript_model,
            "_squeeze_digest",
            return_value=b"\xff" * 32,
        ):
            result = derive_fiat_shamir_transcript(
                CANONICAL_CONSTRUCTION_PLAN,
                STATEMENT_TERM,
                APPLICATION_CONTEXT_TERM,
                CAP0_VALUE,
                CAP1_VALUE,
                TERMINAL_COEFFICIENTS,
                0,
                resources,
            )
        self.assertIsInstance(result, CheckResult)
        assert isinstance(result, CheckResult)
        self.assertIs(
            result.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(result.code, "FRI-IOR-TRANSCRIPT-027")
        self.assertEqual(resources.sampler_attempts, 3)

    def test_grinding_search_exhausts_the_selected_resource_budget(self) -> None:
        resources = ResourceCounter(
            _request_limits(
                hash_calls=32,
                hash_bytes=1 << 14,
                sampler_attempts=8,
                grinding_trials=3,
            )
        )

        def reject_with_charge(
            _work_seed: bytes,
            _nonce: int,
            selected: ResourceCounter | None = None,
        ) -> bool:
            assert selected is not None
            selected.consume_grinding_trials(1)
            return False

        with (
            patch.object(
                transcript_model,
                "_work_succeeds",
                side_effect=reject_with_charge,
            ),
            self.assertRaises(ModelFailure) as raised,
        ):
            transcript_model._find_grinding_nonce(  # noqa: SLF001
                b"\x00" * 32,
                resources,
            )
        self.assertIs(
            raised.exception.outcome,
            OutcomeClass.DETERMINISTIC_LIMIT_EXCEEDED,
        )
        self.assertEqual(raised.exception.code, "FRI-IOR-TRANSCRIPT-035")
        self.assertEqual(resources.grinding_trials, 3)


if __name__ == "__main__":
    unittest.main()
