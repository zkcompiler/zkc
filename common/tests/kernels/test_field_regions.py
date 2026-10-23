"""All nominal field families across structured maps, eager checks and Host execution."""

import random

import pytest

from binary_reference import BASE, CUBIC, cubic_add, cubic_mul, mul, readable
from binomial_reference import FIELDS as BINOMIAL, P
from entry import Entry

PRIMES = {
    'bls12-381.fr': 52435875175126190479447740508185965837690552500527637822603658699938581184513,
    'bn254.fr': 21888242871839275222246405745257275088548364400416034343698204186575808495617,
    'ristretto255.scalar': 2**252 + 27742317777372353535851937790883648493,
}
SOURCE = '''module sample;
domain F = field("FIELD");
type Vector<E:Field> = builtin("vector", E);
math fn formula(x:F, y:F, a:F, unused:F)->F {
  let u=x*y+a; let v=x*y+a; return (u+v)*(x-y)+a;
}
fn work(xs:Vector<F>, ys:Vector<F>, unused:Vector<F>, a:F)->Vector<F> {
  return map formula(each xs, each ys, a, each unused);
}
protocol Run roles(P)(xs:Vector<F>@P, ys:Vector<F>@P, unused:Vector<F>@P, a:F@P)
 -> (value:Vector<F>@P) { return work(xs,ys,unused,a); }
entry fn Demo(inputs:Run::Inputs) { return Run::run(inputs); }
'''


def arithmetic(field, rng):
    if field in PRIMES:
        q = PRIMES[field]
        return (lambda: rng.randrange(q), lambda a, b: (a + b) % q,
                lambda a, b: (a - b) % q, lambda a, b: a * b % q, str)
    if field in BINOMIAL:
        algebra = BINOMIAL[field]
        wire = (lambda a: str(a[0])) if algebra.degree == 1 else (lambda a: list(map(str, a)))
        return (lambda: [rng.randrange(P) for _ in range(algebra.degree)], algebra.add,
                lambda a, b: [(x-y) % P for x, y in zip(a, b, strict=True)], algebra.mul, wire)
    if field == BASE:
        return lambda: rng.getrandbits(64), lambda a, b: a ^ b, lambda a, b: a ^ b, mul, readable
    assert field == CUBIC
    return lambda: [rng.getrandbits(64) for _ in range(3)], cubic_add, cubic_add, cubic_mul, readable


@pytest.mark.parametrize('field', [*PRIMES, *BINOMIAL, BASE, CUBIC])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--no-finite-bulk')])
def test_structured_field_map_preserves_nominal_arithmetic(toolchain, journal, directory, field, flags):
    entry = Entry(toolchain, journal, directory, SOURCE.replace('FIELD', field), flags)
    sample, add, sub, multiply, wire = arithmetic(field, random.Random(7129))
    for size in (0, 1, 9, 33):
        xs, ys, unused = ([sample() for _ in range(size)] for _ in range(3))
        scalar = sample()
        expected = []
        for x, y in zip(xs, ys, strict=True):
            term = add(multiply(x, y), scalar)
            expected.append(wire(add(multiply(add(term, term), sub(x, y)), scalar)))
        inputs = {'xs': list(map(wire, xs)), 'ys': list(map(wire, ys)),
                  'unused': list(map(wire, unused)), 'a': wire(scalar)}
        assert entry.run(f'size-{size}', inputs)['value'] == expected
        # The unobserved formula operand still imposes an eager map shape check,
        # including when the observed columns are empty.
        inputs['unused'].append(wire(scalar))
        refusal = entry.run(f'unused-shape-{size}', inputs, refuses='entry-host-run-failed')
        assert 'rejected:require' in str(refusal)
