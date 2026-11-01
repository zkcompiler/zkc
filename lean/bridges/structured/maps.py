#!/usr/bin/env python3
"""Compare complete map/realization source clients with independent equations."""

import argparse
import copy
import json
from pathlib import Path
import sys

from check import MODULUS, ROOT, definition, fixture, returned as closed_returned
from open_protocol import OpenSuite, returned, stopped


def authored(suite, label, stem):
    subject = suite.authored(label, *fixture(stem))
    interface = json.loads((subject[1].parent / "interface.json").read_text(encoding="utf-8"))
    if not (interface["original"] == subject[2][2].removeprefix("sha256:")):
        raise AssertionError('bridges/structured/maps.py:17: interface["original"] == subject[2][2].removeprefix("sha256:")')
    if not (interface["protocol"] == subject[2][3]):
        raise AssertionError('bridges/structured/maps.py:18: interface["protocol"] == subject[2][3]')
    return subject


def roles(subject):
    return definition(subject[2], subject[2][3])[6][1]


def encoded(values):
    return [str(value % MODULUS) for value in values]


def restrict(values, coordinate):
    """Contiguous halves, with the leading coordinate fixed first."""
    if not (len(values) > 0 and len(values) % 2 == 0):
        raise AssertionError('bridges/structured/maps.py:32: len(values) > 0 and len(values) % 2 == 0')
    middle = len(values) // 2
    return [(lo + (hi - lo) * coordinate) % MODULUS
            for lo, hi in zip(values[:middle], values[middle:])]


def prefix_reference(values, dimensions, columns, point):
    if not (columns > 0 and dimensions < 64 and len(values) == (1 << dimensions) * columns):
        return ["stopped", "reject"]
    current = values
    for coordinate in point:
        if dimensions == 0:
            return ["stopped", "reject"]
        current = restrict(current, coordinate)
        dimensions -= 1
    return closed_returned(encoded(current), str(dimensions), str(columns))


def restriction_cases(suite):
    first = authored(suite, "first", "map-first")
    prefix = authored(suite, "prefix", "map-prefix")
    cases = [
        ([2, 7], 1, 1, [3]), ([1, 7, 2, 9], 2, 1, [3, 5]),
        ([1, 7, 2, 9], 1, 2, [5]), ([3, 8, 2, 11, 5, 17, 7, 19], 3, 1, [2, 6]),
        ([3, 8, 2, 11, 5, 17, 7, 19], 2, 2, [6, 2]),
        ([MODULUS - 1, 2, 7, 3], 2, 1, [MODULUS - 2, 5]),
        ([7], 0, 1, []), ([7], 0, 1, [3]), ([2, 7], 1, 1, [3, 5]),
        ([], 0, 1, []), ([1, 2, 3], 1, 1, [2]), ([1, 7], 1, 0, []),
        ([1, 7], 64, 1, []), ([1, 7], 2**64 - 1, 1, []),
    ]
    for index in range(suite.args.cases):
        dimensions, columns = suite.rng.randrange(5), suite.rng.randrange(1, 4)
        values = [suite.rng.randrange(MODULUS) for _ in range((1 << dimensions) * columns)]
        point = [suite.rng.randrange(MODULUS) for _ in range(suite.rng.randrange(dimensions + 2))]
        cases.append((values, dimensions, columns, point))
    for index, (values, dimensions, columns, point) in enumerate(cases):
        inputs = [encoded(values), str(dimensions), str(columns), encoded(point)]
        expected = prefix_reference(values, dimensions, columns, point)
        suite.case(f"prefix-{index}", lambda n=index, i=inputs, e=expected:
                   suite.compare(prefix, f"prefix-{n}", i, e))
        coordinate = point[0] if point else 7
        inputs = [encoded(values), str(dimensions), str(columns), str(coordinate)]
        expected = prefix_reference(values, dimensions, columns, [coordinate])
        suite.case(f"first-{index}", lambda n=index, i=inputs, e=expected:
                   suite.compare(first, f"first-{n}", i, e))
    return first, prefix


def map_site(subject):
    targets = {item[1] for item in subject[2][7] if item[0] == "collect"}
    found = [row[4] for item in subject[2][7] if item[0] == "function"
             for row in item[9][1] if row[0][0] == "apply" and row[0][1] in targets]
    if not (len(found) == 1):
        raise AssertionError(found)
    return found[0]


def local_site(subject):
    calls = [row for row in definition(subject[2], subject[2][3])[9][1]
             if row[0][0] == "local_call"]
    if not (len(calls) == 1):
        raise AssertionError(calls)
    return calls[0][4]


def formula_cases(suite):
    combination = authored(suite, "combination", "map-combination")
    constant = authored(suite, "constant", "map-constant")
    for index, (a, b, unused, s, t) in enumerate([
        ([], [], [], 2, 5), ([1], [7], [19], 2, 5),
        ([1, 7, 2], [9, 3, 11], [0, 0, 0], 2, 5),
        ([MODULUS - 1, 7], [9, MODULUS - 3], [31, 41], MODULUS - 2, 11),
        ([1, 7], [9], [0, 0], 2, 5), ([1, 7], [9, 3], [0], 2, 5),
        ([], [], [0], 2, 5),
    ]):
        inputs = [str(s), encoded(a), str(t), encoded(b), encoded(unused), "23"]
        valid = len(a) == len(b) == len(unused)
        expected = (returned([encoded([s*x-t*y+3 for x, y in zip(a, b)])]) if valid
                    else stopped("refused", map_site(combination)))
        suite.case(f"combination-{index}", lambda n=index, i=inputs, e=expected:
                   suite.compare_open(combination, f"combination-{n}", roles(combination)[0], i, [], e))
    for index, (a, b) in enumerate([([], []), ([1, 7], [2, 9]), ([1, 7], [2]), ([], [9])]):
        inputs = [encoded(a), encoded(b), "23"]
        expected = returned([encoded([7] * len(a))]) if len(a) == len(b) else stopped("refused", map_site(constant))
        suite.case(f"constant-{index}", lambda n=index, i=inputs, e=expected:
                   suite.compare_open(constant, f"constant-{n}", roles(constant)[0], i, [], e))
    for label, subject, inputs, missing in [
        ("combination", combination, ["2", ["1"], "5", ["7"], ["0"], "23"], (4, 5)),
        ("constant", constant, [["1"], ["7"], "23"], (1, 2)),
    ]:
        suite.case(label + "-nonowner", lambda n=label, s=subject, i=inputs:
                   suite.compare_open(s, n + "-nonowner", roles(s)[1], [None] * len(i), [], returned([None])))
        for index in missing:
            absent = copy.deepcopy(inputs); absent[index] = None
            suite.case(f"{label}-missing-{index}", lambda n=f"{label}-missing-{index}", s=subject, i=absent:
                       suite.compare_open(s, n, roles(s)[0], i, [], stopped("incomplete", local_site(s))))
    return combination, constant


def source_variants(suite, combination):
    """Exercise body-sensitive interpretation independently of source naming."""
    source = combination[0].read_text(encoding="utf-8")
    declaration = next(item for item in combination[2][7] if item[0] == "realize")
    formula = declaration[4]
    if not (source.count(formula) == 2):
        raise AssertionError('bridges/structured/maps.py:134: source.count(formula) == 2')
    literal = '#algebra.literal<<"bls12-381.fr">, 3 : ui255> : !algebra.field<"bls12-381.fr">'
    if source.count(literal) != 1:
        raise AssertionError("expected one typed Fr literal with value 3")
    variants = [
        ("renamed-formula", source.replace(formula, "renamed_formula"), 3),
        ("changed-formula", source.replace(literal, literal.replace('3 : ui255', '5 : ui255')), 5),
    ]
    for label, changed, offset in variants:
        subject = suite.export(label, changed, combination[2][3])
        if not (subject[2][2] != combination[2][2]):
            raise AssertionError('bridges/structured/maps.py:142: subject[2][2] != combination[2][2]')
        inputs = ["2", ["1", "7"], "5", ["9", "3"], ["0", "0"], "23"]
        expected = returned([encoded([2*x-5*y+offset for x, y in zip([1, 7], [9, 3])])])
        suite.case(label, lambda n=label, s=subject, i=inputs, e=expected:
                   suite.compare_open(s, n, roles(s)[0], i, [], e))


def realization_cases(suite):
    subject = authored(suite, "values", "realization-values")
    for index, (values, dimensions, columns) in enumerate([
        ([7], 0, 1), ([1, 7, 2, 9], 2, 1), ([1, 7, 2, 9], 1, 2),
        ([], 0, 1), ([1, 7], 1, 0), ([1, 7], 2**64 - 1, 1),
    ]):
        valid = columns > 0 and dimensions < 64 and len(values) == (1 << dimensions) * columns
        expected = closed_returned(encoded(values)) if valid else ["stopped", "reject"]
        inputs = [encoded(values), str(dimensions), str(columns)]
        suite.case(f"values-{index}", lambda n=index, i=inputs, e=expected:
                   suite.compare(subject, f"values-{n}", i, e))
    return subject


def declaration_controls(suite, combination, realization):
    # These are adversarial retained snapshots, not claims that their digest
    # identifies mutated native bytes. The independent reader must reject them.
    data = combination[2]
    collection = next(item for item in data[7] if item[0] == "collect")
    variants = []
    for label, mutate, code in [
        ("collection-missing-body", lambda row: row.__setitem__(6, "missing_helper"), "structured-unknown-helper"),
        ("collection-scalar-result", lambda row: row.__setitem__(4, [["apply", "field", [["domain", "Field", "bls12-381.fr"]]]]), "structured-formation"),
        ("collection-extra-field", lambda row: row.append("unrepresented"), "structured-definition"),
        ("collection-truncated-inputs", lambda row: row.__setitem__(3, row[3][:-1]), "structured-formation"),
        ("collection-missing-predicate", lambda row: row.__setitem__(7, "missing_predicate"), "structured-unknown-helper"),
    ]:
        bad = copy.deepcopy(data); mutate(definition(bad, collection[1]))
        variants.append((label, bad, code))
    for label, position in [("collection-body-inputs", 4), ("collection-body-results", 5)]:
        bad = copy.deepcopy(data); definition(bad, collection[6])[position] = []
        variants.append((label, bad, "structured-operand" if position == 4 else "structured-formation"))
    bad = copy.deepcopy(data)
    unused = copy.deepcopy(collection); unused[1] = "unused_bad_collection"; unused[6] = "missing_helper"
    bad[7].append(unused)
    variants.append(("unused-invalid-collection", bad, "structured-unknown-helper"))
    bad = copy.deepcopy(data); bad[7].append(copy.deepcopy(collection))
    variants.append(("duplicate-collection", bad, "structured-duplicate-symbol"))
    for label, name in [("collection-name-empty", ""), ("collection-name-limit", "x" * 513)]:
        bad = copy.deepcopy(data); unused = copy.deepcopy(collection); unused[1] = name
        bad[7].append(unused); variants.append((label, bad, "structured-string"))
    for label, mutate, code in [
        ("domain-forward-reference", lambda row: row[3].__setitem__(2, ["zip", [2, 0]]), "structured-domain-reference"),
        ("domain-empty-zip", lambda row: row[3].__setitem__(2, ["zip", []]), "structured-domain-operands"),
        ("domain-missing-result", lambda row: row.__setitem__(4, 99), "structured-domain-reference"),
    ]:
        bad = copy.deepcopy(data); mutate(bad[4][0]); variants.append((label, bad, code))
    # Collection callbacks are ordinary effectful helpers; their complete ABI
    # and closure are checked even for a predicate that would skip every item.
    bad = copy.deepcopy(data)
    root = definition(bad, bad[3]); root[4] = copy.deepcopy(collection[3]); root[5] = copy.deepcopy(collection[4])
    owner = root[6][1][0]; root[6][2] = [[owner] for _ in root[4]]; root[6][3] = [[owner]]
    root[9] = ["block", [[["local_call", collection[1], owner], list(range(len(root[4]))),
                          copy.deepcopy(collection[4]), [], "direct_collection"]], ["return", [0]]]
    variants.append(("collection-direct-protocol-call", bad, "structured-call-kind"))
    real_data = realization[2]
    real = next(item for item in real_data[7] if item[0] == "realize")
    bad = copy.deepcopy(real_data); definition(bad, real[1])[3] = []
    variants.append(("realize-output-abi", bad, "structured-formation"))
    bad = copy.deepcopy(real_data); definition(bad, real[4])[3] = "public"
    variants.append(("realize-public-helper", bad, "structured-header"))
    bad = copy.deepcopy(real_data); definition(bad, real[1]).append([])
    variants.append(("realize-extra-field", bad, "structured-definition"))
    for label, snapshot, code in variants:
        suite.case(label, lambda n=label, s=snapshot, c=code: suite.refuse_snapshot(n, s, c))


def run_cases(suite):
    restriction_cases(suite)
    combination, _ = formula_cases(suite)
    source_variants(suite, combination)
    realization = realization_cases(suite)
    declaration_controls(suite, combination, realization)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--reference", type=Path, default=ROOT / "build/compiler/test/zkc-structured_reference-test")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=8)
    parser.add_argument("--seed", type=int, default=43619)
    parser.add_argument("--write-fixtures", action="store_true")
    args = parser.parse_args(); args.runtime = None
    return OpenSuite(args).run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
