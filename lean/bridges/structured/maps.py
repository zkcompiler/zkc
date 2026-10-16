#!/usr/bin/env python3
"""Compare complete map/realization source clients with independent equations."""

import argparse
import copy
import json
from pathlib import Path
import re
import sys

from check import MODULUS, ROOT, definition, returned as closed_returned
from open_protocol import OpenSuite, returned, stopped


def modules():
    sources = [ROOT / "compiler/test/fixtures/structured-source/map-callers.zkc",
               *sorted((ROOT / "libraries/zkc").glob("*.zkc"))]
    result = {}
    for path in sources:
        name = re.search(r"^module\s+([\w:]+)\s*;", path.read_text(encoding="utf-8"), re.M)
        if name is None or name[1] in result:
            raise ValueError(f"invalid or duplicate source module: {path}")
        result[name[1]] = path
    return result


def authored(suite, label, entry, stem, namespace):
    subject = suite.authored(label, "map_examples::" + entry, modules(), (stem, namespace))
    interface = json.loads((subject[1].parent / "interface.json").read_text(encoding="utf-8"))
    assert interface["original"] == subject[2][2].removeprefix("sha256:")
    assert interface["protocol"] == subject[2][3]
    return subject


def roles(subject):
    return definition(subject[2], subject[2][3])[6][1]


def encoded(values):
    return [str(value % MODULUS) for value in values]


def restrict(values, coordinate):
    """Contiguous halves, with the leading coordinate fixed first."""
    assert len(values) > 0 and len(values) % 2 == 0
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
    first = authored(suite, "first", "FirstEntry", "map-first", "MapFirst")
    prefix = authored(suite, "prefix", "PrefixEntry", "map-prefix", "MapPrefix")
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
    targets = {item[1] for item in subject[2][7] if item[0] == "map"}
    found = [row[4] for item in subject[2][7] if item[0] == "function"
             for row in item[9][1] if row[0][0] == "apply" and row[0][1] in targets]
    assert len(found) == 1, found
    return found[0]


def local_site(subject):
    calls = [row for row in definition(subject[2], subject[2][3])[9][1]
             if row[0][0] == "local_call"]
    assert len(calls) == 1, calls
    return calls[0][4]


def formula_cases(suite):
    combination = authored(suite, "combination", "LinearCombinationEntry", "map-combination", "MapCombination")
    constant = authored(suite, "constant", "ConstantRowsEntry", "map-constant", "MapConstant")
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
    declaration = next(item for item in combination[2][7] if item[0] == "map")
    formula = declaration[4]
    assert source.count(formula) == 2
    assert source.count('value = "3"') == 1
    variants = [
        ("renamed-formula", source.replace(formula, "renamed_formula"), 3),
        ("changed-formula", source.replace('value = "3"', 'value = "5"'), 5),
    ]
    for label, changed, offset in variants:
        subject = suite.export(label, changed, combination[2][3])
        assert subject[2][2] != combination[2][2]
        inputs = ["2", ["1", "7"], "5", ["9", "3"], ["0", "0"], "23"]
        expected = returned([encoded([2*x-5*y+offset for x, y in zip([1, 7], [9, 3])])])
        suite.case(label, lambda n=label, s=subject, i=inputs, e=expected:
                   suite.compare_open(s, n, roles(s)[0], i, [], e))


def realization_cases(suite):
    subject = authored(suite, "values", "RealizeValuesEntry", "realization-values", "RealizationValues")
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
    mapping = next(item for item in data[7] if item[0] == "map")
    variants = []
    for label, mask in [
        ("mask-numeric", [1 if row else 0 for row in mapping[5]]),
        ("mask-string", [str(row).lower() for row in mapping[5]]),
        ("mask-short", mapping[5][:-1]),
        ("mask-empty", []),
        ("mask-all-broadcast", [False] * len(mapping[5])),
    ]:
        bad = copy.deepcopy(data); definition(bad, mapping[1])[5] = mask
        variants.append((label, bad))
    for label, mutate in [
        ("map-missing-helper", lambda row: row.__setitem__(4, "missing_helper")),
        ("map-scalar-result", lambda row: row.__setitem__(3, [["field", "bls12-381.fr"]])),
        ("map-extra-field", lambda row: row.append("unrepresented")),
    ]:
        bad = copy.deepcopy(data); mutate(definition(bad, mapping[1]))
        variants.append((label, bad))
    bad = copy.deepcopy(data)
    definition(bad, mapping[4])[3] = "public"
    variants.append(("map-public-helper", bad))
    bad = copy.deepcopy(data)
    duplicate = copy.deepcopy(mapping); duplicate[1] = "unused_bad_mask"; duplicate[5] = []
    bad[7].append(duplicate)
    variants.append(("unused-invalid-map", bad))
    bad = copy.deepcopy(data); bad[7].append(copy.deepcopy(mapping))
    variants.append(("duplicate-map", bad))
    for label, name in [("map-name-slash", "bad/name"), ("map-name-limit", "x" * 129)]:
        bad = copy.deepcopy(data); unused = copy.deepcopy(mapping); unused[1] = name
        bad[7].append(unused); variants.append((label, bad))
    # A dead zero-result call still belongs to the formula closure. Its body is
    # ordinarily valid Math, but equality is outside the map ring fragment.
    field = ["field", "bls12-381.fr"]
    bad = copy.deepcopy(data)
    bad[7].append(["function", "dead_equality", "math", "private", [field], [], [], [], [],
                   ["block", [[["field.equal", field[1]], [0, 0], [["bool"]], [], ""]], ["return", []]]])
    definition(bad, mapping[4])[9][1].append([["call", "dead_equality"], [0], [], [], ""])
    variants.append(("map-dead-transitive-equality", bad))
    # A preparation declaration is not a protocol-local-call target, even when
    # a forged protocol supplies an exactly matching signature.
    bad = copy.deepcopy(data)
    root = definition(bad, bad[3]); root[4] = copy.deepcopy(mapping[2]); root[5] = copy.deepcopy(mapping[3])
    owner = root[6][1][0]; root[6][2] = [[owner] for _ in root[4]]; root[6][3] = [[owner]]
    root[9] = ["block", [[["local_call", mapping[1], owner], list(range(len(root[4]))),
                          copy.deepcopy(mapping[3]), [], "direct_map"]], ["return", [0]]]
    variants.append(("map-direct-protocol-call", bad))
    real_data = realization[2]
    real = next(item for item in real_data[7] if item[0] == "realize")
    bad = copy.deepcopy(real_data); definition(bad, real[1])[3] = []
    variants.append(("realize-output-abi", bad))
    bad = copy.deepcopy(real_data); definition(bad, real[4])[3] = "public"
    variants.append(("realize-public-helper", bad))
    bad = copy.deepcopy(real_data); definition(bad, real[1]).append([])
    variants.append(("realize-extra-field", bad))
    diagnostics = {
        "mask-numeric": "structured-map-mask", "mask-string": "structured-map-mask",
        "mask-short": "structured-header", "mask-empty": "structured-header",
        "mask-all-broadcast": "structured-header", "map-missing-helper": "structured-unknown-helper",
        "map-scalar-result": "structured-map", "map-extra-field": "structured-definition",
        "map-public-helper": "structured-header", "unused-invalid-map": "structured-header",
        "duplicate-map": "structured-duplicate-symbol", "map-name-slash": "structured-header",
        "map-name-limit": "structured-header", "map-dead-transitive-equality": "structured-map",
        "map-direct-protocol-call": "structured-call-kind", "realize-output-abi": "structured-realization",
        "realize-public-helper": "structured-header", "realize-extra-field": "structured-definition",
    }
    assert set(diagnostics) == {label for label, _ in variants}
    for label, snapshot in variants:
        suite.case(label, lambda n=label, s=snapshot: suite.refuse_snapshot(n, s, diagnostics[n]))


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
