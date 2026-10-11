"""Nested matrix collection admission and values through source and native Host.

Dense integer arithmetic is the value reference. The tests compare logical
shape stops under sufficient capacity, without asserting resource identity.
"""
import json
from pathlib import Path

import pytest

from entry import Entry
from input_files import decimal_values

ROOT = Path(__file__).resolve().parents[3]
SOURCE = (ROOT / 'compiler/test/fixtures/language/nested-matrix.zkc').read_text()


def matrix(rows, columns, entries, tag, width):
    payload = b''.join(n.to_bytes(4, 'little') for n in (rows, columns, len(entries)))
    payload += b''.join(r.to_bytes(4, 'little') + c.to_bytes(4, 'little')
                        + value.to_bytes(width, 'little') for r, c, value in entries)
    return {'wire': (b'ZKCV\x00' + bytes([tag]) + payload).hex()}


def source(field, columns, ignored=False):
    text = SOURCE.replace('"koala-bear"', f'"{field}"')
    if columns:
        text = text.replace('indices.rows', 'indices.columns').replace('matrix.row', 'matrix.column')
    if ignored:
        text = text.replace('xs:Vector<F>,seed:F', 'xs:Vector<F>,ignored:Vector<F>,seed:F')
        text = text.replace('xs:Vector<F>@P,seed:F@P', 'xs:Vector<F>@P,ignored:Vector<F>@P,seed:F@P')
        text = text.replace('work(m,xs,seed)', 'work(m,xs,ignored,seed)')
        text = text.replace('zip(row_values(m,r),elements(xs))',
                            'zip(zip(row_values(m,r),elements(xs)),elements(ignored))')
        text = text.replace('fn(s,(a,b))', 'fn(s,((a,b),_))')
    return text


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk']])
@pytest.mark.parametrize('columns', [False, True])
@pytest.mark.parametrize('field,tag,width', [('koala-bear', 25, 4), ('bls12-381.fr', 23, 32)])
def test_nested_matrix_values_and_empty_admission(toolchain, journal, directory,
                                                flags, columns, field, tag, width):
    entry = Entry(toolchain, journal, directory, source(field, columns, ignored=True), flags)
    sparse = [(0, 0, 2), (0, 2, 3), (1, 1, 5)]
    values = [7, 11] if columns else [7, 11, 13]
    dense = [[2, 0, 3], [0, 5, 0]]
    products = ([sum(dense[r][c] * values[r] for r in range(2)) for c in range(3)]
                if columns else [sum(a * b for a, b in zip(row, values, strict=True))
                                 for row in dense])
    for seed in (0, 19):
        inputs = {'m': matrix(2, 3, sparse, tag, width),
                  'xs': decimal_values(values), 'ignored': decimal_values([0] * len(values)),
                  'seed': decimal_values(seed)}
        assert entry.run(f'ordinary-{seed}', inputs)['result'] == decimal_values(
            [seed + product for product in products])
    for label, changed in [('used', {'xs': decimal_values([])}),
                           ('ignored', {'ignored': decimal_values([])})]:
        refused = entry.run(label, inputs | changed, refuses='entry-run-incomplete')
        assert 'rejected:require' in json.dumps(refused)

    # Empty outer traversal skips *all* inner admission, even conflicting zip
    # lengths. This is observably different from an eagerly checked matvec.
    outer_empty = (3, 0) if columns else (0, 3)
    empty_inputs = {'m': matrix(*outer_empty, [], tag, width),
                    'xs': decimal_values([5]), 'ignored': decimal_values([7, 11]),
                    'seed': decimal_values(19)}
    assert entry.run('empty-outer-conflicting-inner', empty_inputs)['result'] == []

    # An entered, empty inner fold still admits its zip and returns its seed in
    # every row/column. The contraction's additive identity is insufficient.
    inner_empty = (0, 2) if columns else (2, 0)
    zero_inputs = {'m': matrix(*inner_empty, [], tag, width),
                   'xs': decimal_values([]), 'ignored': decimal_values([]),
                   'seed': decimal_values(19)}
    assert entry.run('empty-inner-nonzero-seed', zero_inputs)['result'] == decimal_values([19, 19])
    refused = entry.run('empty-inner-ignored-mismatch',
                        zero_inputs | {'ignored': decimal_values([1])},
                        refuses='entry-run-incomplete')
    assert 'rejected:require' in json.dumps(refused)
    both_empty = zero_inputs | {'m': matrix(0, 0, [], tag, width),
                                'xs': decimal_values([1]), 'ignored': decimal_values([2, 3])}
    assert entry.run('both-empty-skips-admission', both_empty)['result'] == []
