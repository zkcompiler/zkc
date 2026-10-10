"""Octic kernels through a .zkc Entry, with an independent integer oracle.

The reference is convolution modulo X^8 - 3 over KoalaBear. Neither compiler
operations nor the backend's extension implementation compute expected values.
"""

import random

import pytest

from entry import Entry
from octic_reference import P, ZERO, add, mul, power

X = [0, 1] + [0] * 6
X7 = [0] * 7 + [1]

SOURCE = '''module sample;
domain E = field("koala-bear.ext8-binomial3");
type Vector<F:Field> = builtin("vector", F);
type Matrix<F:Field> = builtin("matrix", F);
fn work(a:E, b:E, xs:Vector<E>, m:Matrix<E>) -> (E,E,Vector<E>,E,Vector<E>,Vector<E>,E) {
  let product = a * b;
  let inverse = kernel<E>("field.inverse", a);
  let scaled = kernel<E>("vector.scale", xs, b);
  let dot = kernel<E>("vector.dot", xs, scaled);
  let mv = kernel<E>("matrix.mul_vector", m, xs);
  let tmv = kernel<E>("matrix.transpose_mul_vector", m, xs);
  let bilinear = kernel<E>("matrix.bilinear", m, xs, xs);
  return (product, inverse, scaled, dot, mv, tmv, bilinear);
}
protocol Run roles(P)(a:E@P, b:E@P, xs:Vector<E>@P, m:Matrix<E>@P)
  -> (result:(E,E,Vector<E>,E,Vector<E>,Vector<E>,E)@P) {
  let result @P = work(a,b,xs,m);
  return (result=result);
}
run Demo = Run;
'''


def wire(kind, value):
    if kind == 'field':
        return [str(x) for x in value]
    if kind == 'vector':
        return [wire('field', x) for x in value]
    return {'rows': '2', 'columns': '2',
            'entries': [[str(r), str(c), wire('field', a)] for r, c, a in value]}


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_octic_kernel_results_and_zero_inverse(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, SOURCE, flags)
    rng = random.Random(917)
    def value():
        return [rng.randrange(P) for _ in range(8)]
    cases = [('wrap', X, X7, [X, X7], [[0, 1, X7], [1, 0, X]])]
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
        expected = [('field', mul(a, b)), ('field', power(a, P**8 - 2)),
                    ('vector', scaled), ('field', dot), ('vector', mv), ('vector', tmv),
                    ('field', add(mul(xs[0], mv[0]), mul(xs[1], mv[1])))]
        assert actual == [wire(kind, result) for kind, result in expected]
    inputs['a'] = wire('field', ZERO)
    report = entry.run('zero-inverse', inputs, refuses='entry-run-incomplete')
    assert 'zero-inverse' in str(report)
    # Malformed noncanonical coordinates are refused before values reach a kernel.
    inputs['a'] = wire('field', [P] + [0] * 7)
    entry.run('noncanonical-field', inputs, refuses=True)
