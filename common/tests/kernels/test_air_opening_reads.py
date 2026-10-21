"""Only witness reads consume ordered AIR opening weights."""

import pytest

from coset_reference import CosetReference
from entry import Entry, joint_execution
from source_modules import library_modules


@pytest.mark.parametrize('field', ['koala-bear', 'koala-bear.ext4-binomial3'])
def test_witness_filter_and_weight_continuation(toolchain, journal, directory, field):
    f = CosetReference(field)
    source = f'''module sample;
use air::table as air;
use zkc::coset as coset;
use zkc::vector::{{Vector}};
use zkc::indices::{{Indices}};
domain F=field("{field}");
protocol Work roles(P)(kind:Indices@P,column:Indices@P,rotation:Indices@P,
    assignments:Vector<F>@P,xs:Vector<F>@P,initial:Vector<F>@P,
    zeta:F@P,rho:F@P,first:F@P)->(out:Vector<F>@P,next:F@P) {{
  let batch=coset::column_batch(coset::coset_domain<F>(3,4),2,xs);
  let slots=air::Inputs {{ kind, column, rotation }};
  let result=air::read_quotients(slots,batch,assignments,4,zeta,rho,initial,first);
  return(out=result.0,next=result.1);
}}
run Demo(inputs: Work::Inputs) {{ return Work::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, library_modules('relations/air'))
    def dense(seed):
        return tuple(seed * (coordinate + 1) % f.modulus for coordinate in range(f.degree))

    columns = [[dense(11 + 3*c + r) for r in range(4)] for c in range(2)]
    initial = [dense(17 + r) for r in range(4)]
    data = {'kind': [0, 1, 2, 3, 1], 'column': [999, 1, 999, 999, 0],
            'rotation': [999, 1, 999, 999, 3],
            'assignments': list(map(f.encode, map(dense, [31, 7, 37, 41, 9]))),
            'xs': [f.encode(x) for column in columns for x in column],
            'initial': list(map(f.encode, initial)), 'zeta': f.encode(f.embed(5))}
    domain = f.domain(f.embed(3), 4)
    unit_domain = f.domain(f.one, 4)
    for rho, first in [(7, 5), (0, 5), (7, 0)]:
        result = initial.copy()
        weight = dense(first)
        for column, rotation, claim in [(1, 1, 7), (0, 3, 9)]:
            point = f.mul(f.embed(5), unit_domain[rotation])
            for i, x in enumerate(domain):
                quotient = f.mul(f.sub(columns[column][i], dense(claim)),
                                 f.power(f.sub(x, point), f.modulus**f.degree - 2))
                result[i] = f.add(result[i], f.mul(weight, quotient))
            weight = f.mul(weight, dense(rho))
        assert entry.run(f'weights-{rho}-{first}', data | {
            'rho': f.encode(dense(rho)), 'first': f.encode(dense(first))}) == {
                'out': list(map(f.encode, result)), 'next': f.encode(weight)}
    assert entry.run('no-witness', data | {'kind': [0, 2, 2, 3, 0],
                     'rho': f.encode(dense(7)), 'first': f.encode(dense(5))}) == {
                         'out': list(map(f.encode, initial)), 'next': f.encode(dense(5))}

    # The library must not weaken native descriptor checks when weights vanish,
    # or skip initial extent validation when no witness read is selected.
    zero_weights = data | {'rho': f.encode(f.zero), 'first': f.encode(f.zero)}
    for name, changes, cause in [
            ('invalid-witness-column', {'column': [999, 2, 999, 999, 0]},
             'refused:coset-coordinate'),
            ('invalid-witness-rotation', {'rotation': [999, 4, 999, 999, 3]},
             'refused:coset-coordinate'),
            ('zero-weight-pole', {'zeta': f.encode(f.embed(3))},
             'refused:coset-opening-point'),
            ('empty-short-initial', {'kind': [0, 2, 2, 3, 0], 'initial': data['initial'][:-1]},
             'refused:coset-opening-shape')]:
        report = entry.run(name, zero_weights | changes, refuses='entry-host-run-failed')
        assert joint_execution(report)['roles'][0]['after'][1]['cause'] == [
            'backend', {'omitted_bytes': 0, 'text': cause}]
