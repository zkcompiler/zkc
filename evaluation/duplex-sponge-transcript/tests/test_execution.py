from __future__ import annotations

import copy
from dataclasses import replace
import json
from pathlib import Path
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(MODEL_ROOT))

from duplexmodel.construction import construction_id, parse_construction  # noqa: E402
from duplexmodel.diagnostics import (  # noqa: E402
    DeterministicLimitExceeded,
    InstanceBoundExceeded,
    MalformedInput,
    ReplayContextMismatch,
)
from duplexmodel.execution import (  # noqa: E402
    derive_generation_prefix_challenges,
    independent_replay,
    parse_public_inputs,
    parse_public_proof,
    replay,
)


CASES = REPO_ROOT / "evaluation/duplex-sponge-transcript/cases"


def loaded(name: str) -> object:
    return json.loads((CASES / name).read_text(encoding="utf-8"))


class ExecutionTest(unittest.TestCase):
    def setUp(self) -> None:
        self.construction_value = loaded("construction.json")
        self.input_value = loaded("public-inputs.json")
        self.proof_value = loaded("public-proof.json")
        self.construction = parse_construction(self.construction_value)
        self.inputs = parse_public_inputs(self.input_value)
        self.proof = parse_public_proof(
            self.proof_value, self.construction, self.inputs
        )

    def test_public_replay_has_exact_challenges_and_resource_trace(self) -> None:
        record = replay(self.construction, self.inputs, self.proof)
        self.assertEqual(record.challenges, ((1, 0), 2, (4, 2, 2, 2)))
        self.assertEqual(record.total_permutation_calls, 5)
        self.assertEqual(len(record.trace), 8)
        self.assertEqual(
            tuple(event.kind for event in record.trace),
            (
                "Start",
                "AbsorbSalt",
                "AbsorbMessage",
                "SqueezeChallenge",
                "AbsorbMessage",
                "SqueezeChallenge",
                "AbsorbMessage",
                "SqueezeChallenge",
            ),
        )

    def test_public_and_independent_replay_agree_exactly(self) -> None:
        primary = replay(self.construction, self.inputs, self.proof)
        independent = independent_replay(self.construction, self.inputs, self.proof)
        self.assertEqual(primary.to_term(), independent.to_term())

    def test_verifier_executes_final_squeeze_while_support_simulates_prefix(self) -> None:
        prefix = derive_generation_prefix_challenges(
            self.construction, self.inputs, self.proof
        )
        record = replay(self.construction, self.inputs, self.proof)
        self.assertEqual(prefix, ((1, 0), 2))
        self.assertEqual(record.challenges[:2], prefix)
        self.assertEqual(len(record.challenges), 3)

    def test_missing_wrong_length_and_late_salt_are_malformed(self) -> None:
        mutations = []
        missing = copy.deepcopy(self.proof_value)
        del missing["salt"]
        mutations.append(missing)
        wrong_length = copy.deepcopy(self.proof_value)
        wrong_length["salt"] = [2]
        mutations.append(wrong_length)
        late = copy.deepcopy(self.proof_value)
        late["late_salt"] = late.pop("salt")
        mutations.append(late)
        for value in mutations:
            with self.subTest(value=value):
                with self.assertRaises(MalformedInput):
                    parse_public_proof(value, self.construction, self.inputs)

    def test_serialized_challenge_is_forbidden_extra_proof_material(self) -> None:
        value = copy.deepcopy(self.proof_value)
        value["challenge-1"] = [3, 3]
        with self.assertRaisesRegex(MalformedInput, "keys differ"):
            parse_public_proof(value, self.construction, self.inputs)

    def test_missing_extra_and_reordered_messages_are_refused(self) -> None:
        missing = copy.deepcopy(self.proof_value)
        missing["prover_messages"].pop()
        extra = copy.deepcopy(self.proof_value)
        extra["prover_messages"].append([0, 0])
        reordered = copy.deepcopy(self.proof_value)
        reordered["prover_messages"][0], reordered["prover_messages"][1] = (
            reordered["prover_messages"][1],
            reordered["prover_messages"][0],
        )
        for value in (missing, extra, reordered):
            with self.subTest(value=value):
                with self.assertRaises(MalformedInput):
                    parse_public_proof(value, self.construction, self.inputs)

    def test_runtime_instance_changes_execution_not_construction_identity(self) -> None:
        baseline_id = construction_id(self.construction)
        value = copy.deepcopy(self.input_value)
        value["statement"]["second"] = 8
        changed_inputs = parse_public_inputs(value)
        changed_proof = parse_public_proof(
            self.proof_value, self.construction, changed_inputs
        )
        changed = replay(self.construction, changed_inputs, changed_proof)
        baseline = replay(self.construction, self.inputs, self.proof)
        self.assertEqual(construction_id(self.construction), baseline_id)
        self.assertNotEqual(changed.challenges, baseline.challenges)

    def test_salt_changes_execution_not_construction_identity(self) -> None:
        baseline_id = construction_id(self.construction)
        value = copy.deepcopy(self.proof_value)
        value["salt"] = [1, 4]
        proof = parse_public_proof(value, self.construction, self.inputs)
        changed = replay(self.construction, self.inputs, proof)
        baseline = replay(self.construction, self.inputs, self.proof)
        self.assertEqual(construction_id(self.construction), baseline_id)
        self.assertNotEqual(changed.challenges, baseline.challenges)

    def test_public_validation_limits_do_not_change_semantic_identity(self) -> None:
        baseline_id = construction_id(self.construction)
        value = copy.deepcopy(self.input_value)
        value["public_resource_limits"]["max_permutation_calls"] = 4
        limited = parse_public_inputs(value)
        with self.assertRaisesRegex(
            DeterministicLimitExceeded, "validation limit exhausted"
        ):
            replay(self.construction, limited, self.proof)
        self.assertEqual(construction_id(self.construction), baseline_id)

    def test_instance_bound_is_defended_in_all_three_execution_paths(self) -> None:
        narrowed = replace(self.construction, instance_bit_bound=8)
        prepared = parse_public_proof(self.proof_value, narrowed, self.inputs)
        for operation in (
            replay,
            independent_replay,
            derive_generation_prefix_challenges,
        ):
            with self.subTest(operation=operation.__name__):
                with self.assertRaisesRegex(
                    InstanceBoundExceeded, "instance_bit_bound"
                ):
                    operation(narrowed, self.inputs, prepared)

    def test_prepared_replay_refuses_a_different_construction_context(self) -> None:
        value = copy.deepcopy(self.construction_value)
        value["construction"]["provider_semantics"]["permutation"]["offset"][0] = 2
        changed = parse_construction(value)
        with self.assertRaisesRegex(ReplayContextMismatch, "not prepared"):
            replay(changed, self.inputs, self.proof)
        rebound = parse_public_proof(self.proof_value, changed, self.inputs)
        changed_record = replay(changed, self.inputs, rebound)
        baseline = replay(self.construction, self.inputs, self.proof)
        self.assertNotEqual(changed_record.challenges, baseline.challenges)

    def test_proof_bytes_cannot_inject_replay_context_identifiers(self) -> None:
        for key in ("core_id", "construction_id", "protocol_id", "invocation_id"):
            with self.subTest(key=key):
                value = copy.deepcopy(self.proof_value)
                value[key] = "sha256:" + "00" * 32
                with self.assertRaisesRegex(MalformedInput, "keys differ"):
                    parse_public_proof(value, self.construction, self.inputs)
