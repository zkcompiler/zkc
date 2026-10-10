"""A pointwise map, the Ring provider and the coset kernels on one product.

The same `x * y` is a `math fn` under `map`, the captured product arena under
`ring.rows` and `ring.coefficients`, and a formal product whose coset
evaluations the map reproduces. Every expectation is integer arithmetic in
KoalaBear[X]/(X^8 - 3): coefficient convolution for the formal product, direct
evaluation at coset points, and reduction modulo `X^n - s^n` for the interpolant
of the pointwise products. No native result is an oracle for another.
"""

import json
import random
from pathlib import Path

import pytest

from entry import Entry
from octic_reference import P, ZERO, ONE, add, mul, power

ROOT = Path(__file__).resolve().parents[3]
ARENA = ROOT / 'examples/projects/expression-sumcheck/product.ring.json'
ROOT_OF_UNITY = 1791270792  # The public KoalaBear two-adic generator of order 2^24.

SOURCE = '''module sample;
domain F = field("{field}");
type Vector<E: Field> = builtin("vector", E);
type Polynomial<E: Field> = builtin("polynomial", E);
domain Product = ring(asset product);
math fn product<E: Field>(x: E, y: E) -> E {{ return x * y; }}
math fn product_ignoring<E: Field>(x: E, y: E, unused: E) -> E {{ return x * y; }}
fn work(p: Vector<F>, q: Vector<F>, shift: F, n: index, m: index, z: F)
    -> (Vector<F>, Vector<F>, Vector<F>, Vector<F>, index, F, F, index) {{
  let left = kernel<F>("poly.from_coefficients", p);
  let right = kernel<F>("poly.from_coefficients", q);
  let left_values = kernel<F>("poly.coset_evaluate", left, shift, n);
  let right_values = kernel<F>("poly.coset_evaluate", right, shift, n);
  let other_values = kernel<F>("poly.coset_evaluate", left, shift, m);
  let mapped = map product_ignoring(each left_values, each right_values, each other_values);
  let rows = kernel<F>("ring.rows",
                       kernel<F>("vector.interleave", left_values, right_values), n; Product);
  let width = kernel<F>("vector.length", p);
  let product_coefficients = kernel<F>("ring.coefficients", kernel<F>("vector.concat", p, q), width; Product);
  let interpolated = kernel<F>("poly.coset_interpolate", mapped, shift);
  let coefficients = kernel<F>("poly.coefficients", interpolated);
  let count = kernel<F>("poly.coefficient_count", interpolated);
  let off_domain = kernel<F>("poly.univariate_evaluate", interpolated, z);
  let formal_off_domain = kernel<F>("poly.univariate_evaluate", left, z)
                        * kernel<F>("poly.univariate_evaluate", right, z);
  let degree = index<Product::Degree>();
  return (mapped, rows, product_coefficients, coefficients, count, off_domain, formal_off_domain, degree);
}}
protocol Run roles(P)(p: Vector<F> @P, q: Vector<F> @P, shift: F @P, n: index @P,
                      m: index @P, z: F @P)
    -> (result: (Vector<F>, Vector<F>, Vector<F>, Vector<F>, index, F, F, index) @P) {{
  let result @P = work(p, q, shift, n, m, z);
  return (result = result);
}}
run Demo = Run;
'''


def wire(kind, value, extension):
    def scalar(v):
        return [str(x) for x in v] if extension else str(v[0])
    return scalar(value) if kind == 'field' else [scalar(v) for v in value]


def evaluate(coefficients, point):
    result, exponent = ZERO, ONE
    for coefficient in coefficients:
        result = add(result, mul(coefficient, exponent))
        exponent = mul(exponent, point)
    return result


def convolve(left, right):
    result = [ZERO] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] = add(result[i + j], mul(x, y))
    return result


def reduce_on_coset(coefficients, shift, n):
    """The unique polynomial of degree below n agreeing on the coset.

    Every coset point satisfies X^n = shift^n, so each coefficient of X^(i + k n)
    moves to X^i scaled by shift^(n k). This is independent of interpolation.
    """
    reduced = [ZERO] * n
    for j, coefficient in enumerate(coefficients):
        reduced[j % n] = add(reduced[j % n], mul(coefficient, power(shift, n * (j // n))))
    while reduced and reduced[-1] == ZERO:
        reduced.pop()
    return reduced


def coset(shift, n):
    root = pow(ROOT_OF_UNITY, (1 << 24) // n, P)
    assert pow(root, n, P) == 1 and pow(root, n // 2, P) == P - 1
    return [mul(shift, [pow(root, i, P)] + [0] * 7) for i in range(n)]


@pytest.mark.parametrize('extension', [False, True])
def test_map_ring_provider_and_formal_product_agree(toolchain, journal, directory, extension):
    field = 'koala-bear' + ('.ext8-binomial3' if extension else '')
    entry = Entry(toolchain, journal, directory, SOURCE.format(field=field),
                  [f'--asset=product=ring-json={ARENA}'])
    rng = random.Random(2711)

    def scalar():
        return [rng.randrange(P) for _ in range(8)] if extension else [rng.randrange(P)] + [0] * 7

    # (width, coset size): the product has degree 2 * (width - 1).
    for width, n in [(3, 4), (3, 8), (5, 8), (2, 2)]:
        p, q = [scalar() for _ in range(width)], [scalar() for _ in range(width)]
        shift, z = scalar(), scalar()
        points = coset(shift, n)
        formal = convolve(p, q)
        pointwise = [mul(evaluate(p, x), evaluate(q, x)) for x in points]
        assert pointwise == [evaluate(formal, x) for x in points]
        reduced = reduce_on_coset(formal, shift, n)
        recovered = 2 * (width - 1) < n
        assert recovered == (reduced == formal)
        inputs = {'p': wire('vector', p, extension), 'q': wire('vector', q, extension),
                  'shift': wire('field', shift, extension), 'n': n, 'm': n,
                  'z': wire('field', z, extension)}
        result = entry.run(f'width{width}-coset{n}', inputs)['result']
        expected = [wire('vector', pointwise, extension),  # map of the math fn
                    wire('vector', pointwise, extension),  # ring.rows of the arena
                    wire('vector', formal, extension),  # ring.coefficients: the formal product
                    wire('vector', reduced, extension),  # interpolant of the pointwise products
                    str(len(reduced)),
                    wire('field', evaluate(reduced, z), extension),
                    wire('field', evaluate(formal, z), extension),
                    '2']  # Product::Degree, with every input weighted one
        assert result == expected, (width, n)
        assert len(formal) == 2 * width - 1 and len(reduced) <= n
        # Off the coset the interpolant and the formal product agree only when recovered.
        assert (result[5] == result[6]) == recovered, (width, n)

    # Unequal row counts stop the map before any arithmetic, also for the
    # column the product never reads.
    inputs['m'] = 2 * inputs['n']
    refused = entry.run('unread-column-shape', inputs, refuses='entry-run-incomplete')
    assert 'rejected:require' in json.dumps(refused)
