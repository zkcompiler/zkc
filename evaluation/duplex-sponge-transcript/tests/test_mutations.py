from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest


MODEL_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(MODEL_ROOT))

from duplexmodel.construction import parse_construction  # noqa: E402
from duplexmodel.execution import (  # noqa: E402
    parse_public_inputs,
    parse_public_proof,
    replay,
)
from duplexmodel.mutations import (  # noqa: E402
    omitted_final_verifier_squeeze,
    prefix_xof_challenges,
    reabsorbed_challenge_schedule,
    salt_after_first_message_challenges,
    transition_mutation_kills,
)


CASES = REPO_ROOT / "evaluation/duplex-sponge-transcript/cases"


def loaded(name: str) -> object:
    return json.loads((CASES / name).read_text(encoding="utf-8"))


class MutationTest(unittest.TestCase):
    def setUp(self) -> None:
        self.construction = parse_construction(loaded("construction.json"))
        self.inputs = parse_public_inputs(loaded("public-inputs.json"))
        self.proof = parse_public_proof(
            loaded("public-proof.json"), self.construction, self.inputs
        )

    def test_nine_source_law_substitutions_are_killed(self) -> None:
        expected = replay(self.construction, self.inputs, self.proof).challenges
        results = transition_mutation_kills(
            self.construction,
            self.inputs,
            self.proof,
            expected,
        )
        self.assertEqual(
            set(results),
            {
                "EmptyAbsorbAsIdentity",
                "EagerPermutationAtFullRate",
                "CombineInsteadOfOverwrite",
                "RestartOutputStream",
                "ResetSqueezeIndexAfterAbsorbPermutation",
                "PrefixXofSubstitution",
                "SaltAfterFirstMessage",
                "DecodedChallengeReabsorption",
                "OmitFinalVerifierSqueeze",
            },
        )
        self.assertTrue(all(results.values()))

    def test_prefix_xof_substitution_changes_the_challenge_schedule(self) -> None:
        source_challenges = replay(
            self.construction, self.inputs, self.proof
        ).challenges
        substituted = prefix_xof_challenges(
            self.construction, self.inputs, self.proof
        )
        self.assertNotEqual(substituted, source_challenges)

    def test_schedule_mutations_are_actual_distinct_executions(self) -> None:
        source_challenges = replay(
            self.construction, self.inputs, self.proof
        ).challenges
        for operation in (
            salt_after_first_message_challenges,
            reabsorbed_challenge_schedule,
            omitted_final_verifier_squeeze,
        ):
            with self.subTest(operation=operation.__name__):
                self.assertNotEqual(
                    operation(self.construction, self.inputs, self.proof),
                    source_challenges,
                )
