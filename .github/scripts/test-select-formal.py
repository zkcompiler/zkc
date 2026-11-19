"""Exercise selection for shared imports, harness changes, source files and docs."""

from pathlib import Path
import runpy
import unittest


selector = runpy.run_path(str(Path(__file__).with_name("select-formal.py")))
select, all_suites = selector["select"], selector["ALL"]


class FormalSelection(unittest.TestCase):
    def test_shared(self):
        for path in ("lean/compiler/Zkc/Core/Process.lean", "lean/compiler/Zkc/Frontend/Elab/Events.lean",
                     "lean/formal/Zkc/Formal/WorldObservation.lean", "lean/formal/lean-toolchain",
                     "lean/formal/lake-manifest.json", "libraries/zkc/polynomial.zkc",
                     "examples/gkr.zkc", ".github/workflows/ci.yml", "justfile"):
            with self.subTest(path=path):
                self.assertEqual(select(["docs/development.md", path]), all_suites)

    def test_controls(self):
        names = ("ChargeConsumers.lean", "OddFork.lean.in", "AuditInteractive.lean")
        self.assertEqual(select(["lean/formal/checks/" + name for name in names]),
                         ("test-interactive", "test-written-knowledge", "test-written-charge"))

    def test_issuer_and_shared_change(self):
        issuer = "lean/formal/Zkc/Tools/Formal/DrawCharge.lean"
        self.assertEqual(select([issuer]), ("test-written-charge",))
        self.assertEqual(select([issuer, "lean/compiler/Zkc/Frontend/Written/Root.lean"]), all_suites)

    def test_documentation(self):
        self.assertEqual(select(["docs/development.md", "docs/figures/verifier.svg", "README.md", "lean/formal/README.md"]), ())


if __name__ == "__main__":
    unittest.main()
