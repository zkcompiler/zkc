"""Direct coset point evaluation against independent integer controls."""

import pytest

from coset_reference import CosetReference
from entry import Entry
from source_modules import library_modules


FIELDS = ('bn254.fr', 'koala-bear', 'koala-bear.ext4-binomial3',
          'koala-bear.ext8-binomial3')
FLAGS = ([], ['--no-simplify'], ['--release-storage'])


def scalar(reference, seed):
    return tuple((pow(seed + 3, coordinate + 2, reference.modulus)
                  + 7 * seed + 11 * coordinate + 1) % reference.modulus
                 for coordinate in range(reference.degree))


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('flags', FLAGS)
def test_coset_points_match_polynomials_arbitrary_words_and_exact_refusals(
        toolchain, journal, directory, field, flags):
    f = CosetReference(field)
    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
fn evaluate(xs:Vector<F>,width:index,height:index,shift:F,point:F)
    ->(Vector<F>,Vector<F>,F,F) {{
  let alias=xs;
  let result=kernel<F>("poly.coset_evaluate_at",xs,width,height,shift,point);
  return(result,alias,shift,point);
}}
protocol Work roles(P)(xs:Vector<F>@P,width:index@P,height:index@P,shift:F@P,point:F@P)
    ->(result:(Vector<F>,Vector<F>,F,F)@P) {{
  return evaluate(xs,width,height,shift,point);
}}
run Demo=Work;
'''
    entry = Entry(toolchain, journal, directory, source, flags)

    def check(name, columns, height, shift, point, expected):
        data = {'xs': [f.encode(x) for column in columns for x in column],
                'width': len(columns), 'height': height,
                'shift': f.encode(shift), 'point': f.encode(point)}
        assert entry.run(name, data)['result'] == [list(map(f.encode, expected)), data['xs'],
                                                  data['shift'], data['point']]
        return data

    # Full degree, zero, constant and a different full-degree column expose
    # truncation, transposition and column-order mistakes. Extension shifts and
    # off-domain points have every coordinate populated.
    shift = scalar(f, 3)
    for height in (1, 4, 8):
        coefficients = [[scalar(f, 19 * column + i + 1) for i in range(height)]
                        for column in range(4)]
        coefficients[1], coefficients[2] = [], [scalar(f, 101)]
        domain = f.domain(shift, height)
        columns = [[f.horner(cs, point) for point in domain] for cs in coefficients]
        for row, point in enumerate(domain):
            check(f'polynomial-h{height}-row{row}', columns, height, shift, point,
                  [column[row] for column in columns])
        for name, point in [('zero', f.zero), ('dense', scalar(f, 7))]:
            assert point not in domain
            data = check(f'polynomial-h{height}-{name}', columns, height, shift, point,
                         [f.horner(cs, point) for cs in coefficients])

    # These values are authored directly, with no polynomial or native
    # interpolation roundtrip involved in their construction or expectation.
    height, shift = 4, scalar(f, 5)
    columns = [[scalar(f, 101 * column + 17 * row + 13) for row in range(height)]
               for column in range(3)]
    domain = f.domain(shift, height)
    for i, point in enumerate([f.zero, scalar(f, 9), *domain]):
        expected = [f.lagrange(column, domain, point) for column in columns]
        if point in domain:
            assert expected == [column[domain.index(point)] for column in columns]
        data = check(f'arbitrary-word-{i}', columns, height, shift, point, expected)

    def refuse(name, changes, cause):
        report = entry.run(name, data | changes, refuses='entry-run-incomplete')
        assert report['execution']['roles'][0]['after'][1]['cause'] == [
            'backend', {'omitted_bytes': 0, 'text': cause}]

    for name, changes, cause in [
            ('short-shape', {'xs': data['xs'][:-1]}, 'refused:coset-batch-shape'),
            ('long-shape', {'xs': data['xs'] + [f.encode(f.one)]}, 'refused:coset-batch-shape'),
            ('wrong-width', {'width': 4}, 'refused:coset-batch-shape'),
            ('zero-height', {'height': 0, 'xs': []}, 'refused:coset-size'),
            ('non-power-height', {'height': 3, 'xs': data['xs'][:9]}, 'refused:coset-size'),
            ('zero-shift', {'shift': f.encode(f.zero)}, 'refused:coset-zero-shift'),
            ('extent-overflow', {'width': 2**64 - 1}, 'exhausted:size-overflow')]:
        refuse(name, changes, cause)

    for height in (0, 1, 3, 2**64 - 1):
        check(f'empty-unused-domain-{height}', [], height, f.zero, scalar(f, 7), [])
    refuse('empty-shape', {'width': 0, 'height': 0, 'shift': f.encode(f.zero),
                           'xs': [f.encode(f.one)]}, 'refused:coset-batch-shape')


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('flags', FLAGS)
def test_coset_point_library_exports_preserve_checked_carriers_and_column_bounds(
        toolchain, journal, directory, field, flags):
    f = CosetReference(field)
    source = f'''module sample;
use zkc::coset as c;
use zkc::vector::{{Vector}};
use zkc::vector as v;
domain F=field("{field}");
fn inspect(xs:Vector<F>,width:index,height:index,shift:F,point:F,column:index)
    ->(F,Vector<F>,F,Vector<F>,Vector<F>,index,index,F) {{
  let batch=c::column_batch(c::coset_domain(shift,height),width,xs);
  let geometry=c::batch_domain(batch);
  let (single,selected,word_values)=if width==0 {{
    (0,0,v::empty<F>())
  }} else {{
    let word=c::word(v::slice(xs,0,height),shift);
    (c::evaluate_at(word,point),c::column_at(xs,column,height,point,shift),c::values(word))
  }};
  return(single,c::evaluate_columns(batch,point),selected,c::batch_values(batch),
    word_values,c::batch_width(batch),c::domain_size(geometry),c::domain_shift(geometry));
}}
protocol Work roles(P)(xs:Vector<F>@P,width:index@P,height:index@P,shift:F@P,
    point:F@P,column:index@P)->(single:F@P,columns:Vector<F>@P,selected:F@P,
    data:Vector<F>@P,word_values:Vector<F>@P,width:index@P,height:index@P,shift:F@P) {{
  let (single,columns,selected,data,word_values,batch_width,batch_height,batch_shift)=
    inspect(xs,width,height,shift,point,column);
  return(single=single,columns=columns,selected=selected,data=data,word_values=word_values,
    width=batch_width,height=batch_height,shift=batch_shift);
}}
run Demo=Work;
'''
    entry = Entry(toolchain, journal, directory, source,
                  [*library_modules('core/polynomial'), *flags])
    height, width, shift = 4, 3, scalar(f, 3)
    domain = f.domain(shift, height)
    columns = [[scalar(f, 53 * column + 7 * row + 1) for row in range(height)]
               for column in range(width)]
    data = {'xs': [f.encode(x) for column in columns for x in column],
            'width': width, 'height': height, 'shift': f.encode(shift)}
    for i, point in enumerate([f.zero, scalar(f, 7), *domain]):
        expected = [f.encode(f.lagrange(column, domain, point)) for column in columns]
        for column in range(width):
            assert entry.run(f'exports-point{i}-column{column}',
                             data | {'point': f.encode(point), 'column': column}) == {
                'single': expected[0], 'columns': expected, 'selected': expected[column],
                'data': data['xs'], 'word_values': data['xs'][:height],
                'width': str(width), 'height': str(height), 'shift': data['shift']}
    for column in (width, width + 1):
        entry.run(f'column-out-of-bounds-{column}',
                  data | {'point': f.encode(f.zero), 'column': column},
                  refuses='entry-run-incomplete')
    entry.run('checked-shape', data | {'point': f.encode(f.zero), 'column': 0,
                                      'xs': data['xs'][:-1]}, refuses='entry-run-incomplete')
    entry.run('checked-domain', data | {'point': f.encode(f.zero), 'column': 0,
                                       'shift': f.encode(f.zero)}, refuses='entry-run-incomplete')
    entry.run('checked-height', data | {'point': f.encode(f.zero), 'column': 0,
                                       'height': 3, 'xs': data['xs'][:9]},
              refuses='entry-run-incomplete')
    constants = [f.encode(scalar(f, seed)) for seed in (43, 47, 59)]
    for i, point in enumerate([f.zero, shift, scalar(f, 7)]):
        assert entry.run(f'singleton-domain-{i}', data | {
            'xs': constants, 'height': 1, 'point': f.encode(point), 'column': 2}) == {
            'single': constants[0], 'columns': constants, 'selected': constants[2],
            'data': constants, 'word_values': constants[:1],
            'width': str(width), 'height': '1', 'shift': data['shift']}
    assert entry.run('empty-checked-batch', data | {
        'xs': [], 'width': 0, 'point': f.encode(f.zero), 'column': 0}) == {
        'single': f.encode(f.zero), 'columns': [], 'selected': f.encode(f.zero),
        'data': [], 'word_values': [], 'width': '0', 'height': str(height),
        'shift': data['shift']}
