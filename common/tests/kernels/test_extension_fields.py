"""KoalaBear extension kernels through a .zkc Entry, with an integer oracle.

The reference is convolution modulo X^d - 3 over KoalaBear for the octic and
quartic extensions. Neither compiler operations nor the backend's extension
implementation compute expected values.
"""

import random

import pytest

from binomial_reference import FIELDS, P
from entry import Entry

SOURCE = '''module sample;
domain E = field("{field}");
type Vector<F:Field> = builtin("vector", F);
type Matrix<F:Field> = builtin("matrix", F);
fn work(a:E, b:E, xs:Vector<E>, m:Matrix<E>) -> (E,E,Vector<E>,E,Vector<E>,Vector<E>,E) {{
  let product = a * b;
  let inverse = kernel<E>("field.inverse", a);
  let scaled = kernel<E>("vector.scale", xs, b);
  let dot = kernel<E>("vector.dot", xs, scaled);
  let mv = kernel<E>("matrix.mul_vector", m, xs);
  let tmv = kernel<E>("matrix.transpose_mul_vector", m, xs);
  let bilinear = kernel<E>("matrix.bilinear", m, xs, xs);
  return (product, inverse, scaled, dot, mv, tmv, bilinear);
}}
protocol Run roles(P)(a:E@P, b:E@P, xs:Vector<E>@P, m:Matrix<E>@P)
  -> (result:(E,E,Vector<E>,E,Vector<E>,Vector<E>,E)@P) {{
  let result @P = work(a,b,xs,m);
  return (result=result);
}}
run Demo = Run;
'''


def wire(kind, value):
    if kind == 'field':
        return [str(x) for x in value]
    if kind == 'vector':
        return [wire('field', x) for x in value]
    return {'rows': '2', 'columns': '2',
            'entries': [[str(r), str(c), wire('field', a)] for r, c, a in value]}


@pytest.mark.parametrize('field', ['koala-bear.ext8-binomial3', 'koala-bear.ext4-binomial3'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_extension_kernel_results_and_zero_inverse(toolchain, journal, directory, field, flags):
    ext = FIELDS[field]
    d, ZERO, add, mul, power = ext.degree, ext.ZERO, ext.add, ext.mul, ext.power
    X = [0, 1] + [0] * (d - 2)
    TOP = [0] * (d - 1) + [1]
    entry = Entry(toolchain, journal, directory, SOURCE.format(field=field), flags)
    rng = random.Random(917 + d)
    def value():
        return [rng.randrange(P) for _ in range(d)]
    # X * X^(d-1) wraps to the nonresidue three.
    cases = [('wrap', X, TOP, [X, TOP], [[0, 1, TOP], [1, 0, X]])]
    for i in range(4):
        cases.append((f'random{i}', value(), value(), [value(), value()],
                      [[r, c, value()] for r in range(2) for c in range(2)]))
    for name, a, b, xs, matrix in cases:
        inputs = {'a': wire('field', a), 'b': wire('field', b),
                  'xs': wire('vector', xs), 'm': wire('matrix', matrix)}
        actual = entry.run(name, inputs)['result']
        scaled = [mul(x, b) for x in xs]
        dot = add(mul(xs[0], scaled[0]), mul(xs[1], scaled[1]))
        mv, tmv = [ZERO[:], ZERO[:]], [ZERO[:], ZERO[:]]
        for r, c, coefficient in matrix:
            mv[r] = add(mv[r], mul(coefficient, xs[c]))
            tmv[c] = add(tmv[c], mul(coefficient, xs[r]))
        expected = [('field', mul(a, b)), ('field', power(a, P**d - 2)),
                    ('vector', scaled), ('field', dot), ('vector', mv), ('vector', tmv),
                    ('field', add(mul(xs[0], mv[0]), mul(xs[1], mv[1])))]
        assert actual == [wire(kind, result) for kind, result in expected]
    inputs['a'] = wire('field', ZERO)
    report = entry.run('zero-inverse', inputs, refuses='entry-run-incomplete')
    assert 'zero-inverse' in str(report)
    # Malformed noncanonical coordinates are refused before values reach a kernel.
    inputs['a'] = wire('field', [P] + [0] * (d - 1))
    entry.run('noncanonical-field', inputs, refuses=True)
