"""Authority-boundary tests for the public replay resource policy."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import sys
import unittest

PACKAGE = Path(__file__).resolve().parents[1]
ROOT = PACKAGE.parents[1]
sys.path.insert(0, str(PACKAGE))

from friiormodel.fixtures import load_fixture, parse_replay_policy  # noqa: E402
from friiormodel.profile import EXACT_ALGEBRA_PROFILE  # noqa: E402
from friiormodel.terms import ModelFailure  # noqa: E402


POLICY_PATH = "evaluation/native-fri-ior/cases/replay-policy.json"
EXPECTED_AUTHORITY = "repository-frozen-report-local-operational-policy"
EXPECTED_CLAIMS = {
    "part_of_protocol_semantics": False,
    "proves_resource_optimality": False,
    "semantic_authority": False,
}


def _policy_value() -> dict[str, object]:
    loaded = load_fixture(ROOT, POLICY_PATH, "replay_policy")
    assert isinstance(loaded.value, dict)
    return loaded.value


class ReplayPolicyAuthorityTest(unittest.TestCase):
    def test_frozen_policy_is_report_local_and_explicitly_nonsemantic(self) -> None:
        value = _policy_value()
        limits = parse_replay_policy(value)

        self.assertEqual(value["authority"], EXPECTED_AUTHORITY)
        self.assertEqual(value["claims"], EXPECTED_CLAIMS)
        self.assertEqual(limits.to_term(), value["limits"])

    def test_legacy_request_local_authority_is_rejected(self) -> None:
        value = deepcopy(_policy_value())
        value["authority"] = "request-local-validation-policy"

        with self.assertRaises(ModelFailure) as caught:
            parse_replay_policy(value)
        self.assertEqual(caught.exception.code, "FRI-IOR-FIXTURE-020")

    def test_semantic_authority_claim_is_rejected(self) -> None:
        value = deepcopy(_policy_value())
        assert isinstance(value["claims"], dict)
        value["claims"]["semantic_authority"] = True

        with self.assertRaises(ModelFailure) as caught:
            parse_replay_policy(value)
        self.assertEqual(caught.exception.code, "FRI-IOR-FIXTURE-020")

    def test_operational_limits_do_not_enter_the_algebra_profile_identity(self) -> None:
        before = EXACT_ALGEBRA_PROFILE.identity
        value = deepcopy(_policy_value())
        assert isinstance(value["limits"], dict)
        value["limits"]["hash_calls"] = 129
        parse_replay_policy(value)

        self.assertEqual(EXACT_ALGEBRA_PROFILE.identity, before)


if __name__ == "__main__":
    unittest.main()
