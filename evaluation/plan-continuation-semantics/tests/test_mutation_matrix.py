from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import mutation_probes  # noqa: E402
import reference_model as m  # noqa: E402


class MutationMatrixTests(unittest.TestCase):
    def test_every_declared_mutation_executes_one_exact_outcome_probe(self) -> None:
        matrix = json.loads(
            (ROOT / "cases" / "mutation-matrix.json").read_text(encoding="utf-8")
        )
        names = [item["probe"] for item in matrix["mutations"]]
        self.assertTrue(names)
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(set(names), set(mutation_probes.PROBES))
        for row in matrix["mutations"]:
            with self.subTest(probe=row["probe"]):
                outcome = mutation_probes.PROBES[row["probe"]]()
                self.assertIs(outcome, m.Outcome(row["expected"]))


if __name__ == "__main__":
    unittest.main()
