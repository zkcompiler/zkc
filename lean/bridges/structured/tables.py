#!/usr/bin/env python3
"""Regenerate actual table contracts and check bounded independent model outcomes.

The scalar replay is used only for equality of canonical KoalaBear values.
Native runtime tests own installed execution; exact source formula laws are
proved separately. Neither bounded replay nor admission is correspondence.
"""

import argparse
import copy
import json
from pathlib import Path
import sys

from check import ROOT, definition, fixture, write_json
from open_protocol import OpenSuite, returned, stopped


class TableSuite(OpenSuite):
    def tool_names(self):
        return ("compiler", "lean")

    def evaluate(self, subject, label, role, inputs, expected):
        request = subject[1].parent / (label + ".request.json")
        write_json(request, ["zkc.structured-open-request/0", role, inputs, [], 1000000])
        actual = json.loads(self.command(label, [self.tools["lean"], "open", subject[1], request]))
        if actual != expected:
            raise AssertionError({"actual": actual, "expected": expected})


def run_cases(suite):
    membership = suite.authored("membership", *fixture("table-membership"))
    read = suite.authored("indexed-read", *fixture("table-indexed-read"))
    subject = membership
    cases = [
        ("empty", [], [], True), ("active-miss", [], [(True, 1)], False),
        ("inactive-miss", [], [(False, 1)], True), ("found", [1], [(True, 1)], True),
        ("wrong-table", [2], [(True, 1)], False),
        ("duplicate-queries", [1], [(True, 1), (True, 1)], True),
        ("duplicate-table", [1, 1], [(True, 1)], True),
        ("masked", [1], [(False, 2), (True, 1)], True),
        ("mask-changed", [1], [(True, 2), (True, 1)], False),
        ("max-canonical", [2130706432], [(True, 2130706432)], True),
    ]
    entry = definition(subject[2], subject[2][3])
    owner = entry[6][2][0][0]
    for label, table, queries, expected in cases:
        values = [[str(x) for x in table], [[active, str(x)] for active, x in queries]]
        suite.case(label, lambda n=label, v=values, e=expected:
                   suite.evaluate(subject, n, owner, v, returned([e])))
    for index in range(suite.args.cases):
        table = [suite.rng.randrange(12) for _ in range(suite.rng.randrange(16))]
        queries = [(bool(suite.rng.getrandbits(1)), suite.rng.randrange(12))
                   for _ in range(suite.rng.randrange(16))]
        expected = all(not active or x in table for active, x in queries)
        values = [[str(x) for x in table], [[active, str(x)] for active, x in queries]]
        suite.case(f"membership-{index}", lambda n=index, v=values, e=expected:
                   suite.evaluate(subject, f"membership-{n}", owner, v, returned([e])))
    nonowner = next(role for role in entry[6][1] if role != owner)
    suite.case("nonowner", lambda: suite.evaluate(subject, "nonowner", nonowner,
               [None, None], returned([None])))
    site = next(row[4] for row in entry[9][1] if row[0][0] == "local_call")
    suite.case("missing-query-port", lambda: suite.evaluate(subject, "missing-query-port", owner,
               [[], None], stopped("incomplete", site)))
    owner = definition(read[2], read[2][3])[6][2][0][0]
    for label, table, coordinate, value, expected in [
        ("empty", [], 0, 1, False), ("first", [1, 2], 0, 1, True),
        ("second", [1, 2], 1, 2, True), ("wrong-position", [1, 2], 0, 2, False),
        ("wrong-value", [1, 2], 1, 1, False), ("past-end", [1, 2], 2, 1, False),
        ("max-index", [1, 2], 2**64 - 1, 1, False),
    ]:
        values = [[str(x) for x in table], str(coordinate), str(value)]
        suite.case("read-" + label, lambda n=label, v=values, e=expected:
                   suite.evaluate(read, "read-" + n, owner, v, returned([e])))
    bad = copy.deepcopy(membership[2])
    bad[9][0][0][4].remove("PrimeField")
    suite.case("changed-catalogue", lambda: suite.refuse_snapshot(
        "changed-catalogue", bad, "structured-catalogue-mismatch"))
    bad = copy.deepcopy(read[2])
    bounded = [item for item in bad[7] if item[0] == "function" and item[7]]
    if not bounded:
        raise AssertionError("indexed read lost its bounded callback")
    bounded[0][7] = []
    suite.case("missing-read-bound", lambda: suite.refuse_snapshot("missing-read-bound", bad))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=16)
    parser.add_argument("--seed", type=int, default=51983)
    parser.add_argument("--write-fixtures", action="store_true")
    return TableSuite(parser.parse_args()).run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
