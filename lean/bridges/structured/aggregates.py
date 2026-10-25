#!/usr/bin/env python3
"""Check native aggregate exports with the independent Lean reader and evaluator.

The fixture tests ordered products and finite folds. It does not establish
native execution correspondence or a canonical transcript byte encoding.
"""

import argparse
import copy
import json
from pathlib import Path
import sys

from check import ROOT, Suite, definition, write_json


class AggregateSuite(Suite):
    def tool_names(self):
        return ("compiler", "lean")

    def evaluate(self, subject, label, values, expected):
        query = definition(subject[2], subject[2][3])[4][0][1]
        products = [["product", query[1], query[2],
                     [["bool", active], ["field", "bls12-381.fr", str(value)]]]
                    for active, value in values]
        request = subject[1].parent / (label + ".inputs.json")
        write_json(request, [["sequence", query, products]])
        result = json.loads(self.command(label, [self.tools["lean"], "run", subject[1], request]))
        if result != ["returned", [["bool", expected]]]:
            raise AssertionError(result)


def run_cases(suite):
    source = (ROOT / "compiler/test/fixtures/structured-source/aggregate-fold.mlir").read_text()
    subject = suite.export("aggregate-fold", source)
    for label, values, expected in [
        ("empty", [], True), ("single", [(True, 7)], True),
        ("false-first", [(False, 9), (True, 7)], False),
        ("false-last", [(True, 7), (False, 9)], False),
        ("duplicates", [(True, 7), (True, 7)], True),
    ]:
        suite.case(label, lambda n=label, v=values, e=expected: suite.evaluate(subject, n, v, e))
    for index in range(suite.args.cases):
        values = [(bool(suite.rng.getrandbits(1)), suite.rng.randrange(100))
                  for _ in range(suite.rng.randrange(32))]
        suite.case(f"ordered-{index}", lambda n=index, v=values:
                   suite.evaluate(subject, f"ordered-{n}", v, all(active for active, _ in v)))
    mutations = []
    data = subject[2]
    bad = copy.deepcopy(data)
    definition(bad, "step")[9][1][0][0][1] = 2
    mutations.append(("component-out-of-range", bad, "structured-product-index"))
    bad = copy.deepcopy(data)
    definition(bad, "make")[9][1][0][0][1] = "other"
    mutations.append(("wrong-constructor", bad, "structured-product-constructor"))
    bad = copy.deepcopy(data)
    definition(bad, "step")[4][1][1] = "other"
    mutations.append(("same-shape-wrong-identity", bad, None))
    bad = copy.deepcopy(data)
    definition(bad, "step")[4][1][3].reverse()
    mutations.append(("swapped-components", bad, None))
    bad = copy.deepcopy(data)
    definition(bad, "make")[5][0][3][1] = ["service", "random.bls12-381.fr/0"]
    mutations.append(("dormant-service-component", bad, "structured-header"))
    bad = copy.deepcopy(data)
    definition(bad, "make")[5][0][3][1] = ["field", "missing"]
    mutations.append(("dormant-unknown-domain", bad, None))
    for label, snapshot, code in mutations:
        suite.case(label, lambda n=label, s=snapshot, c=code: suite.refuse_snapshot(n, s, c))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=16)
    parser.add_argument("--seed", type=int, default=91823)
    return AggregateSuite(parser.parse_args()).run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
