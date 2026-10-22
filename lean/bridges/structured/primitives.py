#!/usr/bin/env python3
"""Check unchanged library helpers through original SSA and Lean admission.

Expected answers use table shape, ordered lists and integer arithmetic directly.
The suite retains whole frontend-selected units; it does not slice helper bodies
or use production kernels as an oracle. Agreement is finite evidence.
"""

import argparse
import copy
import json
from pathlib import Path
import sys

from check import MODULUS, ROOT, definition, fixture, returned as closed_returned
from open_protocol import OpenSuite, returned

FIXTURES = ROOT / "compiler/test/fixtures/structured-source"


def authored(suite, label, stem):
    subject = suite.authored(label, *fixture(stem))
    interface = json.loads((subject[1].parent / "interface.json").read_text(encoding="utf-8"))
    if not (interface["original"] == subject[2][2].removeprefix("sha256:")):
        raise AssertionError('bridges/structured/primitives.py:24: interface["original"] == subject[2][2].removeprefix("sha256:")')
    if not (interface["protocol"] == subject[2][3]):
        raise AssertionError('bridges/structured/primitives.py:25: interface["protocol"] == subject[2][3]')
    return subject


def role(subject, index=0):
    return definition(subject[2], subject[2][3])[6][1][index]


def table_cases(suite):
    subjects = {
        "shape": authored(suite, "shape", "primitive-shape"),
        "table": authored(suite, "table", "primitive-table"),
        "halves": authored(suite, "halves", "primitive-halves"),
    }
    cases = [
        ([], 0, 1), ([7], 0, 1), ([1, 7], 1, 1), ([1, 7, 2, 9], 1, 2),
        ([1, 7, 2, 9], 2, 1), ([1, 3, 7, 2, 8, 9], 1, 3),
        ([1, 2, 3], 1, 1), ([1, 2, 3], 0, 3),
        ([1, 7], 0, 1), ([1, 7], 1, 0), ([], 0, 0),
        ([1, 7], 64, 1), ([1, 7], 63, 1),
        ([1, 7], 500_000, 1), ([1, 7], 2**64 - 1, 1),
    ]
    for index, (items, dimensions, columns) in enumerate(cases):
        values = [str(x) for x in items]
        inputs = [values, str(dimensions), str(columns)]
        valid = 0 < columns and dimensions < 64 and len(items) == (1 << dimensions) * columns
        suite.case(f"shape-{index}", lambda i=inputs, v=valid, n=index: suite.compare_open(
            subjects["shape"], f"shape-{n}", role(subjects["shape"]), i, [], returned([v])))
        expected = closed_returned(values, str(dimensions), str(columns)) if valid else ["stopped", "reject"]
        suite.case(f"table-{index}", lambda i=inputs, e=expected, n=index:
                   suite.compare(subjects["table"], f"table-{n}", i, e))
        if valid and dimensions > 0:
            middle = len(items) // 2
            expected = closed_returned(values[:middle], values[middle:])
        else:
            expected = ["stopped", "reject"]
        suite.case(f"halves-{index}", lambda i=inputs, e=expected, n=index:
                   suite.compare(subjects["halves"], f"halves-{n}", i, e))
    # Same admitted source and argument types; only shape/data differ.
    for index in range(suite.args.cases):
        dimensions, columns = suite.rng.randrange(5), suite.rng.randrange(1, 5)
        values = [str(suite.rng.randrange(MODULUS)) for _ in range((1 << dimensions) * columns)]
        inputs = [values, str(dimensions), str(columns)]
        suite.case(f"random-shape-{index}", lambda i=inputs, n=index: suite.compare_open(
            subjects["shape"], f"random-shape-{n}", role(subjects["shape"]), i, [], returned([True])))
        if dimensions:
            middle = len(values) // 2
            expected = closed_returned(values[:middle], values[middle:])
            suite.case(f"random-halves-{index}", lambda i=inputs, e=expected, n=index:
                       suite.compare(subjects["halves"], f"random-halves-{n}", i, e))
    return subjects


def sequence_cases(suite):
    subject = authored(suite, "sequence", "primitive-sequence")
    for index, (items, value, divisor) in enumerate([
        ([], 5, 1), ([3, 8], 5, 2), ([MODULUS - 1, 2], 7, 3),
        ([3, 3], 8, 5), ([0, 0], 0, 1), ([9], 4, 0),
    ]):
        encoded = [str(x) for x in items]
        inputs = [encoded, str(value), str(divisor)]
        if divisor:
            extended = [*items, value]
            total = sum(extended) % MODULUS
            expected = closed_returned([str(x) for x in extended], str(len(extended) // divisor),
                str(len(extended) % divisor), str(len(items)), str(total), False, total == value, [])
        else:
            expected = ["stopped", "refused"]
        suite.case(f"sequence-{index}", lambda i=inputs, e=expected, n=index:
                   suite.compare(subject, f"sequence-{n}", i, e))
    return subject


def pure_index_cases(suite):
    subject = authored(suite, "pure-index", "primitive-pure-index")
    for value in (0, 1, 2**63, 2**64 - 1):
        suite.case(f"pure-index-{value}", lambda v=value: suite.compare_open(
            subject, f"pure-index-{v}", role(subject), [str(v)], [], returned([v == 0])))
    suite.case("pure-index-absent-nonowner", lambda: suite.compare_open(
        subject, "absent", role(subject, 1), [None], [], returned([None])))


def binding_controls(suite, subject):
    # Mutate retained metadata, including an otherwise unused row. Native source
    # controls independently cover exporter admission; these exercise Lean's
    # reader without relying on the exporter to reject a bad declaration first.
    data = subject[2]
    if not (data[6]):
        raise AssertionError("expected retained primitive bindings")
    variants = []
    bad = copy.deepcopy(data); bad[6].append(["binding", "unused_product", "vector.product", ["bls12-381.fr"], ""])
    variants.append(("unsupported-contract", bad))
    bad = copy.deepcopy(data); bad[6].append(["binding", "unused_impl", "index.add", [], "native/index.add"])
    variants.append(("selected-implementation", bad))
    bad = copy.deepcopy(data); bad[6].append(["binding", "unused_bad", "index.add", ["bls12-381.fr"], ""])
    variants.append(("unused-bad-arguments", bad))
    bad = copy.deepcopy(data); bad[6].append(copy.deepcopy(bad[6][0]))
    variants.append(("duplicate-binding", bad))
    bad = copy.deepcopy(data); bad[6].append(["binding", bad[7][0][1], "index.add", [], ""])
    variants.append(("cross-category-name", bad))
    bad = copy.deepcopy(data); bad[6].append(["binding", "slash/name", "index.add", [], ""])
    variants.append(("binding-name-slash", bad))
    bad = copy.deepcopy(data); bad[6].append(["binding", "x" * 257, "index.add", [], ""])
    variants.append(("binding-name-limit", bad))
    bad = copy.deepcopy(data); del bad[6]
    variants.append(("obsolete-envelope", bad))
    for label, snapshot in variants:
        suite.case(label, lambda n=label, s=snapshot: suite.refuse_snapshot(n, s))
    # Valid metadata cannot be used as a callable, even if a symbol happens to
    # have a suggestive name. The malformed call preserves its original ports.
    bad = copy.deepcopy(data)
    root = definition(bad, bad[3])
    calls = [row for row in root[9][1] if row[0][0] == "local_call"]
    if not (calls):
        raise AssertionError('bridges/structured/primitives.py:137: calls')
    calls[0][0][1] = bad[6][0][1]
    suite.case("binding-is-not-callable", lambda: suite.refuse_snapshot("binding-is-not-callable", bad))


def run_cases(suite):
    subjects = table_cases(suite)
    sequence_cases(suite)
    pure_index_cases(suite)
    binding_controls(suite, subjects["shape"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--reference", type=Path, default=ROOT / "build/compiler/test/zkc-structured_reference-test")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=8)
    parser.add_argument("--seed", type=int, default=93481)
    parser.add_argument("--write-fixtures", action="store_true")
    args = parser.parse_args()
    args.runtime = None
    return OpenSuite(args).run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
