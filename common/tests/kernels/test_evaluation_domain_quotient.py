"""Evaluation-form KZG algebra against integer coefficient interpolation."""

import pytest

from binomial_reference import FIELDS, P
from entry import Entry, joint_execution
from source_modules import library_modules


BLS_FR = 52435875175126190479447740508185965837690552500527637822603658699938581184513
FIELD_NAMES = ('bls12-381.fr', 'koala-bear', 'koala-bear.ext4-binomial3',
               'koala-bear.ext8-binomial3')
MODULES = library_modules('commitments/kzg')
SOURCE = '''module sample;
use zkc::vector::{Vector};
use zkc::evaluation_domain as evaluation;
use kzg as kzg;
domain F=field("FIELD_NAME");
fn compute(roots:Vector<F>,data:Vector<F>,z:F)
    ->(Vector<F>,F,F,Vector<F>,bool,index) {
  let unity=evaluation::checked_roots(roots);
  let input=evaluation::evaluations(unity,data);
  let (q,y)=kzg::quotient(input,z);
  let evaluated=kzg::evaluate(input,z);
  let member=kzg::in_domain(unity,z);
  let location=if member { kzg::position(unity,z) } else { evaluation::size(unity) };
  return(evaluation::points(unity),y,evaluated,q,member,location);
}
protocol Run roles(P)(roots:Vector<F>@P,data:Vector<F>@P,z:F@P)
    ->(points:Vector<F>@P,y:F@P,evaluated:F@P,q:Vector<F>@P,
       member:bool@P,location:index@P) {
  let (points,y,evaluated,q,member,location)=compute(roots,data,z);
  return(points=points,y=y,evaluated=evaluated,q=q,member=member,location=location);
}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''


class FieldReference:
    """Prime arithmetic or the independent integer binomial convolution oracle."""

    def __init__(self, field):
        self.extension = FIELDS.get(field)
        self.modulus = BLS_FR if field == 'bls12-381.fr' else P
        self.degree = self.extension.degree if self.extension else 1
        self.zero = (0,) * self.degree
        self.one = self.embed(1)

    def embed(self, value):
        return (value % self.modulus,) + (0,) * (self.degree - 1)

    def add(self, left, right):
        return tuple((x + y) % self.modulus for x, y in zip(left, right, strict=True))

    def sub(self, left, right):
        return tuple((x - y) % self.modulus for x, y in zip(left, right, strict=True))

    def mul(self, left, right):
        if self.extension:
            return tuple(self.extension.mul(left, right))
        return (left[0] * right[0] % self.modulus,)

    def power(self, value, exponent):
        result = self.one
        while exponent:
            if exponent & 1:
                result = self.mul(result, value)
            value, exponent = self.mul(value, value), exponent >> 1
        return result

    def encode(self, value):
        return str(value[0]) if self.degree == 1 else list(map(str, value))


def horner(field, coefficients, point):
    result = field.zero
    for coefficient in reversed(coefficients):
        result = field.add(field.mul(result, point), coefficient)
    return result


def synthetic_quotient(field, coefficients, point):
    """Divide p(X) by X-point; the remainder is p(point), including constants."""
    quotient = [field.zero] * (len(coefficients) - 1)
    carry = coefficients[-1]
    for i in range(len(coefficients) - 2, -1, -1):
        quotient[i] = carry
        carry = field.add(coefficients[i], field.mul(point, carry))
    return quotient, carry


def interpolate_coefficients(field, points, values):
    """Generic Lagrange coefficient products, without roots-of-unity weights."""
    result = [field.zero] * len(points)
    for i, (point, value) in enumerate(zip(points, values, strict=True)):
        basis, denominator = [field.one], field.one
        for j, other in enumerate(points):
            if i == j:
                continue
            product = [field.zero] * (len(basis) + 1)
            for k, coefficient in enumerate(basis):
                product[k] = field.sub(product[k], field.mul(other, coefficient))
                product[k + 1] = field.add(product[k + 1], coefficient)
            basis = product
            denominator = field.mul(denominator, field.sub(point, other))
        assert denominator != field.zero
        weight = field.mul(value, field.power(denominator, field.modulus ** field.degree - 2))
        result = [field.add(current, field.mul(weight, coefficient))
                  for current, coefficient in zip(result, basis, strict=True)]
    return result


def scalar(field, seed):
    return tuple((seed * (i + 1) + i * i + 7) % field.modulus
                 for i in range(field.degree))


def roots(field, count):
    if count == 1:
        return [field.one]
    if (field.modulus - 1) % count == 0:
        base = 7 if field.modulus == BLS_FR else 3
        generator = field.embed(pow(base, (field.modulus - 1) // count, field.modulus))
    else:
        # A cubic root in the extensions is outside the KoalaBear base field.
        # Search only integer coordinate arithmetic, never a native field result.
        assert count == 3 and field.degree > 1
        exponent = (field.modulus ** field.degree - 1) // count
        candidates = ((seed, 1) + (0,) * (field.degree - 2) for seed in range(1, 9))
        generator = next(root for candidate in candidates
                         if (root := field.power(candidate, exponent)) != field.one)
        assert any(generator[1:])
    points = [field.power(generator, i) for i in range(count)]
    assert field.power(generator, count) == field.one
    assert len(set(points)) == count
    return points


def check_polynomial(entry, field, name, points, coefficients, targets):
    values = [horner(field, coefficients, point) for point in points]
    recovered = interpolate_coefficients(field, points, values)
    assert recovered == coefficients + [field.zero] * (len(points) - len(coefficients))
    for number, point in enumerate(targets):
        quotient, value = synthetic_quotient(field, recovered, point)
        assert value == horner(field, coefficients, point)
        expected = [horner(field, quotient, x) for x in points]
        member = point in points
        location = points.index(point) if member else len(points)
        if member:
            derivative = [field.mul(field.embed(i), c) for i, c in enumerate(coefficients) if i]
            assert expected[location] == horner(field, derivative, point)
        result = entry.run(f'{name}-{number}', {
            'roots': list(map(field.encode, points)), 'data': list(map(field.encode, values)),
            'z': field.encode(point)})
        assert result == {
            'points': list(map(field.encode, points)), 'y': field.encode(value),
            'evaluated': field.encode(value), 'q': list(map(field.encode, expected)),
            'member': member, 'location': str(location)}


@pytest.mark.parametrize('field_name', FIELD_NAMES)
def test_quotients_preserve_arbitrary_root_order_and_coefficient_values(
        toolchain, journal, directory, field_name):
    field = FieldReference(field_name)
    entry = Entry(toolchain, journal, directory,
                  SOURCE.replace('FIELD_NAME', field_name), MODULES)
    natural = roots(field, 8)
    # Neither natural, bit-reversed nor a rotation; even the first point is not 1.
    points = [natural[i] for i in (3, 0, 6, 1, 7, 4, 2, 5)]
    outside = scalar(field, 37)
    assert outside not in points
    coefficients = [scalar(field, seed) for seed in (-3, 0, 5, 17, -11, 2, 9, 23)]
    check_polynomial(entry, field, 'dense', points, coefficients,
                     [points[0], points[3], points[-1], field.zero, outside])
    check_polynomial(entry, field, 'singleton', [field.one], [scalar(field, -5)],
                     [field.one, field.zero])
    four = roots(field, 4)
    four = [four[i] for i in (2, 0, 3, 1)]
    check_polynomial(entry, field, 'constant', four, [scalar(field, 11)],
                     [four[-1], field.zero])
    check_polynomial(entry, field, 'zero', four, [field.zero], [four[0], outside])
    if field_name in ('bls12-381.fr', 'koala-bear.ext4-binomial3'):
        three = roots(field, 3)
        three = [three[i] for i in (2, 0, 1)]
        check_polynomial(entry, field, 'non-two-adic', three, coefficients[:3],
                         [three[0], three[-1], field.zero])


@pytest.mark.parametrize('flags', [('--no-simplify',), ('--release-storage',),
                                  ('--no-simplify', '--release-storage',
                                   '--no-finite-bulk', '--no-calculation-batching')])
def test_quotient_branches_and_singletons_with_source_flags(
        toolchain, journal, directory, flags):
    field_name = 'koala-bear.ext4-binomial3'
    field = FieldReference(field_name)
    entry = Entry(toolchain, journal, directory,
                  SOURCE.replace('FIELD_NAME', field_name), (*flags, *MODULES))
    natural = roots(field, 4)
    points = [natural[i] for i in (2, 0, 3, 1)]
    check_polynomial(entry, field, 'flags', points,
                     [scalar(field, seed) for seed in (3, -5, 13, 19)],
                     [points[0], points[-1], scalar(field, 37)])
    check_polynomial(entry, field, 'singleton', [field.one], [field.zero],
                     [field.one, field.zero])


def test_invalid_checked_roots_and_evaluation_extents_reject_before_outputs(
        toolchain, journal, directory):
    field_name = 'koala-bear.ext4-binomial3'
    field = FieldReference(field_name)
    entry = Entry(toolchain, journal, directory,
                  SOURCE.replace('FIELD_NAME', field_name), MODULES)
    one, two, zero = map(field.encode, (field.one, field.embed(2), field.zero))
    negative = field.encode(field.embed(-1))
    valid = {'roots': [negative, one], 'data': [two, one], 'z': zero}
    # Every refusal starts with well-formed wire values. Distinctness, root
    # equations and exact evaluation extents are the checked carriers' duties.
    for name, change in [
            ('empty-domain', {'roots': [], 'data': []}),
            ('duplicate-roots', {'roots': [one, one]}),
            ('non-root', {'roots': [one, two]}),
            ('zero-singleton', {'roots': [zero], 'data': [one]}),
            ('non-root-singleton', {'roots': [two], 'data': [one]}),
            ('short-values', {'data': [one]}),
            ('long-values', {'data': [one, two, zero]})]:
        report = entry.run(name, valid | change, refuses='entry-host-run-failed')
        assert joint_execution(report)['roles'][0]['after'][1]['cause'] == [
            'explicit', {'omitted_bytes': 0, 'text': 'reject'}]
