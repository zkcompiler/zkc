"""The harness reads the installed EVM target declaration and nothing else."""

import json
import unittest

import probe
import target


class TargetDeclarationTests(unittest.TestCase):
    def test_release_profile_is_the_declared_optimizer(self):
        declared = json.loads(target.DATA)["solc"]["optimizer"]
        self.assertEqual(probe.PROFILES["colon"], declared)
        # Each caller gets its own copy.
        target.optimizer()["enabled"] = None
        self.assertEqual(target.optimizer(), declared)

    def test_budget_is_the_fork_cap_or_the_declared_validation_budget(self):
        for name, row in target.FORKS.items():
            with self.subTest(fork=name):
                cap = row["transaction_gas_cap"]
                expected = cap if cap is not None else target.LIMITS["practical_gas"]
                self.assertEqual(target.transaction_gas(name), expected)

    def test_forks_are_exact(self):
        for name, row in target.FORKS.items():
            self.assertIs(target.fork(name), row)
            self.assertIs(target.solc_fork(row["solc"]), row)
        for wrong in ("", "latest", "london", *(row["hardfork"] for row in target.FORKS.values())):
            with self.subTest(fork=wrong), self.assertRaisesRegex(ValueError, "unsupported-fork"):
                target.fork(wrong)
            with self.subTest(solc=wrong), self.assertRaisesRegex(ValueError, "unsupported-fork"):
                target.solc_fork(wrong)


if __name__ == "__main__":
    unittest.main()
