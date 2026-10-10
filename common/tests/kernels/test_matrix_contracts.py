"""Sparse native matrices checked against dense integer arithmetic via Entry."""

import random

import pytest

from entry import Entry

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
run Demo=Run;
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
                           refuses='entry-run-incomplete')
        assert 'matrix-shape' in str(report)
    for name, bad in [
        ('zero', [(0, 1, 0)]), ('duplicate', [(0, 1, 1), (0, 1, 2)]),
        ('unsorted', [(1, 1, 1), (0, 1, 2)]), ('outside', [(0, 3, 1)]),
        ('noncanonical', [(0, 1, modulus)]),
    ]:
        entry.run(name, inputs | {'m': {'wire': matrix_wire(matrix_tag, width, 2, 3, bad)}}, refuses=True)
    entry.run('truncated', inputs | {'m': {'wire': inputs['m']['wire'][:-2]}}, refuses=True)
    entry.run('trailing', inputs | {'m': {'wire': inputs['m']['wire'] + '00'}}, refuses=True)
