"""Sparse native matrices checked against dense integer arithmetic via Entry."""

from source_modules import core_packages, library_modules

import random
from pathlib import Path

import pytest

from binomial_reference import FIELDS as EXTENSIONS
from entry import Entry

ROOT = Path(__file__).resolve().parents[3]
MODULES = library_modules(*core_packages())

FIELDS = [
    ('bls12-381.fr', 23, 66, 1, 32,
     52435875175126190479447740508185965837690552500527637822603658699938581184513),
    ('ristretto255.scalar', 24, 14, 13, 32, 2**252 + 27742317777372353535851937790883648493),
    ('koala-bear', 25, 20, 19, 4, 2130706433),
]


def matrix_wire(tag, width, rows, columns, entries):
    payload = b''.join(n.to_bytes(4, 'little') for n in (rows, columns, len(entries)))
    payload += b''.join(r.to_bytes(4, 'little') + c.to_bytes(4, 'little')
                        + value.to_bytes(width, 'little') for r, c, value in entries)
    return (b'ZKCV\x00' + bytes([tag]) + payload).hex()


def vector_wire(tag, width, values):
    return (b'ZKCV\x00' + bytes([tag]) + len(values).to_bytes(4, 'little')
            + b''.join(x.to_bytes(width, 'little') for x in values)).hex()


@pytest.mark.parametrize('field', ['bls12-381.fr', 'bn254.fr', 'ristretto255.scalar',
                                  'koala-bear', 'koala-bear.ext8-binomial3',
                                  'koala-bear.ext4-binomial3'])
@pytest.mark.parametrize('contract', ['row_dot', 'column_dot'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_matrix_contraction_library(toolchain, journal, directory, field, contract, flags):
    source = f'''module sample;
use zkc::matrix::{{Matrix}};
use zkc::vector::{{Vector}};
domain F=field("{field}");
fn work(m:Matrix<F>,v:Vector<F>,selected:index)->F {{
  return zkc::matrix::{contract}(m,v,selected);
}}
protocol Run roles(P)(m:Matrix<F>@P,v:Vector<F>@P,selected:index@P)->(result:F@P) {{
  return work(m,v,selected);
}}
run Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    row = contract == 'row_dot'
    reference = EXTENSIONS.get(field)
    extension = reference is not None and reference.degree > 1
    if extension:
        ZERO, add, mul = reference.ZERO, reference.add, reference.mul

    def coefficient(n):
        return [n, 1] + [0] * (reference.degree - 3) + [1] if extension else n

    def encode(value):
        return [str(n) for n in value] if extension else str(value)

    entries = [(0, 0, coefficient(3)), (0, 4, coefficient(5)),
               (2, 0, coefficient(7)), (2, 2, coefficient(11))]
    values = [coefficient(n) for n in ([2, 3, 5, 7, 11] if row else [13, 17, 19, 23])]
    inputs = {'m': {'rows': '4', 'columns': '5',
                    'entries': [[str(r), str(c), encode(a)] for r, c, a in entries]},
              'v': [encode(a) for a in values]}
    for selected in range(4 if row else 5):
        expected = ZERO[:] if extension else 0
        for r, c, a in entries:
            if (r if row else c) == selected:
                value = values[c if row else r]
                expected = add(expected, mul(a, value)) if extension else expected + a * value
        assert entry.run(f'selected-{selected}', inputs | {'selected': str(selected)})['result'] == encode(expected)

    for selected in [4 if row else 5, 2**32, 2**64 - 1]:
        report = entry.run(f'bad-index-{selected}', inputs | {'selected': str(selected)},
                           refuses='entry-host-run-failed')
        assert 'matrix-index' in str(report)
    for selected in ['0', str(2**64 - 1)]:
        report = entry.run(f'bad-shape-{selected}', inputs | {'selected': selected, 'v': []},
                           refuses='entry-host-run-failed')
        assert 'matrix-shape' in str(report)

    rows, columns = (65536, 0) if row else (0, 65536)
    zero_inputs = {'m': {'rows': str(rows), 'columns': str(columns), 'entries': []},
                   'v': [], 'selected': '65535'}
    assert entry.run('maximum-selected-empty-inner', zero_inputs)['result'] == encode(ZERO if extension else 0)
    for rows, columns in ([(0, 0), (0, 3)] if row else [(0, 0), (3, 0)]):
        empty_selected = {'m': {'rows': str(rows), 'columns': str(columns), 'entries': []},
                          'v': [encode(coefficient(1)) for _ in range(columns if row else rows)],
                          'selected': '0'}
        report = entry.run(f'empty-selected-{rows}-{columns}', empty_selected,
                           refuses='entry-host-run-failed')
        assert 'matrix-index' in str(report)


@pytest.mark.parametrize('field,matrix_tag,vector_tag,scalar_tag,width,modulus', FIELDS)
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_matrix_shapes_dense_reference_and_malformed_values(
        toolchain, journal, directory, field, matrix_tag, vector_tag, scalar_tag, width, modulus, flags):
    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
type Matrix<E:Field>=builtin("matrix",E);
fn work(m:Matrix<F>,x:Vector<F>,y:Vector<F>)->(Vector<F>,Vector<F>,F,bool) {{
  let mv=kernel<F>("matrix.mul_vector",m,x);
  let tv=kernel<F>("matrix.transpose_mul_vector",m,y);
  let bi=kernel<F>("matrix.bilinear",m,y,x);
  let shape=kernel<F>("matrix.shape_check",m;"2","3");
  return (mv,tv,bi,shape);
}}
protocol Run roles(P)(m:Matrix<F>@P,x:Vector<F>@P,y:Vector<F>@P)
  ->(result:(Vector<F>,Vector<F>,F,bool)@P) {{
  let result @P =work(m,x,y);
  return(result=result);
}}
run Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    rng = random.Random(82731)
    cases = []
    for rows, columns in [(0, 0), (0, 7), (9, 0), (1, 1), (5, 7), (17, 31), (73, 97)]:
        entries = [(r, c, rng.randrange(1, modulus)) for r in range(rows) for c in range(columns)
                   if rng.randrange(5) == 0]
        cases.append((f'random-{rows}-{columns}', rows, columns, entries,
                      [rng.randrange(modulus) for _ in range(columns)],
                      [rng.randrange(modulus) for _ in range(rows)]))
    cases.append(('wraparound', 2, 3, [(0, 1, modulus - 1), (1, 0, modulus - 2), (1, 2, 3)],
                  [modulus - 1, 5, 7], [2, modulus - 1]))
    for name, rows, columns, entries, x, y in cases:
        inputs = {'m': {'wire': matrix_wire(matrix_tag, width, rows, columns, entries)},
                  'x': [str(v) for v in x], 'y': [str(v) for v in y]}
        dense = [[0] * columns for _ in range(rows)]
        for r, c, coefficient in entries:
            dense[r][c] = coefficient
        mv = [sum(dense[r][c] * x[c] for c in range(columns)) % modulus for r in range(rows)]
        tv = [sum(y[r] * dense[r][c] for r in range(rows)) % modulus for c in range(columns)]
        bi = sum(y[r] * dense[r][c] * x[c] for r in range(rows) for c in range(columns)) % modulus
        scalar = str(bi)
        assert entry.run(name, inputs)['result'] == [[str(v) for v in mv],
            [str(v) for v in tv], scalar, (rows, columns) == (2, 3)]

    for name, port, values in [('bad-columns', 'x', [1, 2]), ('bad-rows', 'y', [1])]:
        report = entry.run(name, inputs | {port: [str(v) for v in values]},
                           refuses='entry-host-run-failed')
        assert 'matrix-shape' in str(report)
    for name, bad in [
        ('zero', [(0, 1, 0)]), ('duplicate', [(0, 1, 1), (0, 1, 2)]),
        ('unsorted', [(1, 1, 1), (0, 1, 2)]), ('outside', [(0, 3, 1)]),
        ('noncanonical', [(0, 1, modulus)]),
    ]:
        entry.run(name, inputs | {'m': {'wire': matrix_wire(matrix_tag, width, 2, 3, bad)}}, refuses=True)
    entry.run('truncated', inputs | {'m': {'wire': inputs['m']['wire'][:-2]}}, refuses=True)
    entry.run('trailing', inputs | {'m': {'wire': inputs['m']['wire'] + '00'}}, refuses=True)
