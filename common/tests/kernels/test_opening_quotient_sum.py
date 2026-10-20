"""Weighted off-domain quotients against independent integer field division."""

import pytest

from coset_reference import CosetReference
from entry import Entry


FIELDS = ('bn254.fr', 'koala-bear', 'koala-bear.ext4-binomial3',
          'koala-bear.ext8-binomial3')


def scalar(reference, seed):
    return tuple((pow(seed + 7, coordinate + 2, reference.modulus)
                  + 13 * seed + 3 * coordinate + 1) % reference.modulus
                 for coordinate in range(reference.degree))


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('flags', ([], ['--no-simplify'], ['--release-storage']))
def test_weighted_quotients_preserve_coordinates_aliases_and_refusals(
        toolchain, journal, directory, field, flags):
    f = CosetReference(field)
    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
type Indices=builtin("indices");
fn weighted(xs:Vector<F>,width:index,height:index,shift:F,selected:Indices,
    points:Vector<F>,claims:Vector<F>,weights:Vector<F>,initial:Vector<F>)
    ->Vector<F> {{
  return kernel<F>("poly.opening_quotient_sum",xs,width,height,shift,
    selected,points,claims,weights,initial);
}}
protocol Work roles(P)(xs:Vector<F>@P,width:index@P,height:index@P,shift:F@P,
    selected:Indices@P,points:Vector<F>@P,claims:Vector<F>@P,
    weights:Vector<F>@P,initial:Vector<F>@P)
    ->(result:Vector<F>@P,alias:Vector<F>@P,initial:Vector<F>@P) {{
  let result=weighted(xs,width,height,shift,
    selected,points,claims,weights,initial);
  return(result=result,alias=xs,initial=initial);
}}
run Demo=Work;
'''
    entry = Entry(toolchain, journal, directory, source, flags)

    def check(name, data, expected):
        assert entry.run(name, data) == {
            'result': list(map(f.encode, expected)),
            'alias': data['xs'], 'initial': data['initial']}

    for height in (1, 4, 8):
        shift = scalar(f, 3)
        domain = f.domain(shift, height)
        columns = [[scalar(f, 101 * column + 17 * row + 1) for row in range(height)]
                   for column in range(3)]
        # Repeated columns/points, arbitrary claims and zero coefficients retain
        # their defined arithmetic meaning. No native interpolation is an oracle.
        selected = [2, 0, 2, 1]
        points = [f.zero, scalar(f, 9), f.zero, scalar(f, 11)]
        assert not any(point in domain for point in points)
        claims = [scalar(f, 37 + j) for j in range(4)]
        weights = [scalar(f, 53), f.zero, f.one, scalar(f, 59)]
        initial = [scalar(f, 71 + row) for row in range(height)]
        expected = list(initial)
        for column, point, claim, weight in zip(selected, points, claims, weights, strict=True):
            for row, x in enumerate(domain):
                inverse = f.power(f.sub(x, point), f.modulus ** f.degree - 2)
                quotient = f.mul(f.sub(columns[column][row], claim), inverse)
                expected[row] = f.add(expected[row], f.mul(weight, quotient))
        data = {'xs': [f.encode(x) for column in columns for x in column],
                'width': 3, 'height': height, 'shift': f.encode(shift),
                'selected': selected, 'points': list(map(f.encode, points)),
                'claims': list(map(f.encode, claims)), 'weights': list(map(f.encode, weights)),
                'initial': list(map(f.encode, initial))}
        check(f'dense-{height}', data, expected)
        check(f'empty-{height}', data | {'selected': [], 'points': [], 'claims': [],
                                        'weights': [], 'shift': f.encode(f.zero)}, initial)

    # Run boundaries and a return to a replaced point exercise reuse and
    # recomputation with the same immutable inputs. Zero weights still take
    # part in the complete validation performed before any accumulation.
    point_runs = [(name, [scalar(f, seed) for seed in seeds])
                  for name, seeds in [('same', [9] * 6), ('mixed', [9, 9, 11, 9, 11, 11]),
                                      ('distinct', [9, 11, 13, 15, 17, 19])]]
    point = scalar(f, 9)
    rotated = f.mul(point, f.mul(domain[1], f.power(shift, f.modulus ** f.degree - 2)))
    assert rotated != point and f.power(rotated, height) == f.power(point, height)
    point_runs.append(('equal-powers', [point, rotated, rotated, point, point, rotated]))
    if f.degree > 1:
        # Equal base coordinates must not make distinct extension points alias.
        other = (point[0], (point[1] + 1) % f.modulus, *point[2:])
        point_runs.append(('equal-base-coordinate', [point, other, other, point, point, other]))
    for name, points in point_runs:
        selected = [2, 0, 2, 1, 0, 1]
        claims = [scalar(f, 37 + j) for j in range(6)]
        weights = [scalar(f, 53), f.zero, f.one, scalar(f, 59), f.zero, scalar(f, 61)]
        assert not any(point in domain for point in points)
        expected = list(initial)
        for column, point, claim, weight in zip(selected, points, claims, weights, strict=True):
            for row, x in enumerate(domain):
                inverse = f.power(f.sub(x, point), f.modulus ** f.degree - 2)
                expected[row] = f.add(expected[row],
                                      f.mul(weight, f.mul(f.sub(columns[column][row], claim), inverse)))
        check(f'point-runs-{name}', data | {'selected': selected,
              'points': list(map(f.encode, points)), 'claims': list(map(f.encode, claims)),
              'weights': list(map(f.encode, weights))}, expected)

    def refuse(name, changes, cause):
        report = entry.run(name, data | changes, refuses='entry-run-incomplete')
        assert report['execution']['roles'][0]['after'][1]['cause'] == [
            'backend', {'omitted_bytes': 0, 'text': cause}]

    for name, changes, cause in [
            ('short-batch', {'xs': data['xs'][:-1]}, 'refused:coset-batch-shape'),
            ('extent-overflow', {'width': 2**64 - 1}, 'exhausted:size-overflow'),
            ('short-initial', {'initial': data['initial'][:-1]}, 'refused:coset-opening-shape'),
            ('short-points', {'points': data['points'][:-1]}, 'refused:coset-opening-shape'),
            ('long-claims', {'claims': data['claims']+[f.encode(f.one)]}, 'refused:coset-opening-shape'),
            ('short-weights', {'weights': data['weights'][:-1]}, 'refused:coset-opening-shape'),
            ('last-column', {'selected': [2, 0, 2, 3]}, 'refused:coset-coordinate'),
            ('last-point', {'points': data['points'][:-1]+[f.encode(domain[-1])]},
             'refused:coset-opening-point'),
            ('zero-weight-on-domain', {'points': [data['points'][0], f.encode(domain[1]),
                                                *data['points'][2:]]},
             'refused:coset-opening-point'),
            ('zero-shift', {'shift': f.encode(f.zero)}, 'refused:coset-zero-shift'),
            ('zero-height', {'xs': [], 'height': 0, 'initial': []}, 'refused:coset-size'),
            ('non-power-height', {'xs': data['xs'][:9], 'height': 3,
                                  'initial': data['initial'][:3]}, 'refused:coset-size')]:
        refuse(name, changes, cause)

    for height in (0, 3):
        initial = [scalar(f, i + 19) for i in range(height)]
        check(f'empty-unused-domain-{height}',
              data | {'xs': [], 'width': 0, 'height': height, 'shift': f.encode(f.zero),
                      'selected': [], 'points': [], 'claims': [], 'weights': [],
                      'initial': list(map(f.encode, initial))}, initial)
