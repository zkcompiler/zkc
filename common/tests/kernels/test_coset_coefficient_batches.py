"""Coefficient batches and source splitting against independent integer Horner."""

import pytest

from coset_reference import CosetReference
from entry import Entry, joint_execution
from source_modules import library_modules


FIELDS = ['bn254.fr', 'koala-bear', 'koala-bear.ext4-binomial3',
          'koala-bear.ext8-binomial3']


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_coefficient_batch_order_padding_shrink_and_refusals(
        toolchain, journal, directory, field, flags):
    reference = CosetReference(field)
    encode = reference.encode

    def scalar(seed):
        return tuple((seed*seed + 7*seed + 11*j + 1) % reference.modulus
                     for j in range(reference.degree))

    shift = scalar(3)
    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
fn evaluate(xs:Vector<F>,columns:index,height:index,shift:F,size:index)
    ->(Vector<F>,Vector<F>) {{
  let result=kernel<F>("poly.coset_evaluate_batch",xs,columns,height,shift,size);
  return(result,xs);
}}
protocol Work roles(P)(xs:Vector<F>@P,columns:index@P,height:index@P,shift:F@P,size:index@P)
    ->(result:(Vector<F>,Vector<F>)@P) {{
  return evaluate(xs,columns,height,shift,size);
}}
run Demo(inputs: Work::Inputs) {{ return Work::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, flags)

    def inputs(blocks, height, size):
        padded = [cs + [reference.zero] * (height-len(cs)) for cs in blocks]
        assert all(len(cs) == height for cs in padded)
        expected = [encode(reference.horner(cs, x)) for cs in blocks
                    for x in reference.domain(shift, size)]
        return {'xs': [encode(x) for cs in padded for x in cs],
                'columns': len(blocks), 'height': height,
                'shift': encode(shift), 'size': size}, expected

    for height, size, columns in [(0, 1, 3), (0, 8, 3), (1, 1, 3),
                                  (1, 8, 1), (3, 8, 4), (8, 8, 16), (5, 2, 3)]:
        blocks = [[scalar(19*c+j+1) for j in range(min(height, size))]
                  if c != 0 or columns == 1 else [] for c in range(columns)]
        data, expected = inputs(blocks, height, size)
        assert entry.run(f'batch-{height}-{size}-{columns}', data)['result'] == [expected, data['xs']]

    def refuse(name, data, cause):
        report = entry.run(name, data, refuses='entry-host-run-failed')
        assert joint_execution(report)['roles'][0]['after'][1]['cause'] == [
            'backend', {'omitted_bytes': 0, 'text': cause}]

    blocks = [[], [scalar(13), scalar(17)]]
    data, expected = inputs(blocks, 5, 2)
    assert entry.run('zero-tails', data)['result'] == [expected, data['xs']]
    # A non-base coordinate in the final block's final coefficient must count.
    high = (0,) * (reference.degree-1) + (1,)
    invalid = data | {'xs': data['xs'][:-1] + [encode(high)]}
    refuse('late-nonzero-tail', invalid, 'refused:coset-coefficient-count')
    for name, changes, cause in [
            ('short', {'xs': data['xs'][:-1]}, 'refused:coset-batch-shape'),
            ('long', {'xs': data['xs']+[encode(reference.zero)]}, 'refused:coset-batch-shape'),
            ('zero-output', {'size': 0}, 'refused:coset-size'),
            ('non-two-adic-output', {'size': 3}, 'refused:coset-size'),
            ('zero-shift', {'shift': encode(reference.zero)}, 'refused:coset-zero-shift'),
            ('input-overflow', {'xs': [], 'columns': 2**64-1, 'height': 2}, 'exhausted:size-overflow'),
            ('output-overflow', {'xs': [], 'columns': 2**64-1, 'height': 0}, 'exhausted:size-overflow')]:
        refuse(name, data | changes, cause)
    empty = {'xs': [], 'columns': 0, 'height': 2**64-1, 'size': 2**64-1,
             'shift': encode(reference.zero)}
    assert entry.run('unused-domain', empty)['result'] == [[], []]
    refuse('empty-shape', empty | {'xs': [encode(reference.one)]}, 'refused:coset-batch-shape')
    refuse('zero-height-checks-domain', empty | {'columns': 3, 'height': 0, 'size': 0},
           'refused:coset-size')


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_source_coefficient_helper_and_split_quotient(
        toolchain, journal, directory, field, flags):
    reference = CosetReference(field)
    encode = reference.encode
    source = f'''module sample;
use zkc::coset as coset;
use zkc::vector::{{Vector}};
use air::polynomial::{{split_quotient}};
domain F=field("{field}");
protocol Work roles(P)(values:Vector<F>@P,coefficients:Vector<F>@P,shift:F@P,
    size:index@P,width:index@P,count:index@P)
    ->(split:Vector<F>@P,direct:Vector<F>@P,original:Vector<F>@P) {{
  let split=split_quotient(values,shift,size,width,count);
  let direct=coset::evaluate_batch(coefficients,count,width,shift,size);
  return(split=split,direct=direct,original=coefficients);
}}
run Demo(inputs: Work::Inputs) {{ return Work::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source,
                  [*library_modules('relations/air'), *flags])
    shift = tuple(3+j for j in range(reference.degree))
    coefficients = [tuple(13*i+7*j+1 for j in range(reference.degree)) for i in range(5)]
    values = [encode(reference.horner(coefficients, x))
              for x in reference.domain(shift, 8)]
    for width, count, size in [(3, 2, 8), (3, 4, 4), (2, 3, 8)]:
        padded = coefficients + [reference.zero] * (width*count-len(coefficients))
        expected = [encode(reference.horner(padded[c*width:(c+1)*width], x))
                    for c in range(count) for x in reference.domain(shift, size)]
        data = {'values': values, 'coefficients': list(map(encode, padded)),
                'shift': encode(shift), 'size': size, 'width': width, 'count': count}
        assert entry.run(f'split-{width}-{count}-{size}', data) == {
            'split': expected, 'direct': expected, 'original': data['coefficients']}
    # Interpolation normalization, capacity refusal and representation padding
    # remain source operations before the new batch call.
    refused = entry.run('insufficient-capacity', data | {'width': 2, 'count': 2},
                        refuses='entry-host-run-failed')
    cause = joint_execution(refused)['roles'][0]['after'][1]['cause']
    assert cause[0] == 'explicit' and cause[1]['text'] == 'reject'
    zeros = [encode(reference.zero)] * 8
    data = {'values': zeros, 'coefficients': [], 'shift': encode(shift),
            'size': 3, 'width': 0, 'count': 0}
    assert entry.run('zero-polynomial-zero-columns', data) == {
        'split': [], 'direct': [], 'original': []}
    data = data | {'size': 8, 'count': 3}
    expected = [encode(reference.zero)] * 24
    assert entry.run('zero-polynomial-zero-height', data) == {
        'split': expected, 'direct': expected, 'original': []}
