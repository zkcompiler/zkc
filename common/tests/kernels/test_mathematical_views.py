"""Mathematical interpretation is explicit, checked, and independent of storage."""

import pytest

from entry import Entry
from source_modules import library_modules


MODULES = library_modules('zkc')


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_multilinear_factor_layout(toolchain, journal, directory, flags):
    source = '''module sample;
    use zkc::vector as vec;
    use zkc::multilinear as mle;
    domain F=field("koala-bear");
    fn evaluate(data:vec::Vector<F>,dimensions:index,width:index,point:vec::Vector<F>) {
      let input=mle::table(data,dimensions,width);
      let result=mle::fix_prefix(input,point);
      return (mle::values(result),mle::variables(result),mle::width(result));
    }
    protocol Run roles(P)(data:vec::Vector<F>@P,dimensions:index@P,width:index@P,point:vec::Vector<F>@P)
      ->(result:vec::Vector<F>@P,remaining:index@P,columns:index@P){
      let result=evaluate(data,dimensions,width,point);
      return(result=result.0,remaining=result.1,columns=result.2);
    }run Demo=Run;
    '''
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    # Rows 00,01,10,11; two independent factors at each row. Not column-major.
    values = [1, 2, 3, 5, 7, 11, 13, 17]
    point = [2, 3]
    result = entry.run('factors', {'data': list(map(str, values)), 'dimensions': '2',
                                 'width': '2', 'point': list(map(str, point))})
    weights = [2, -3, -4, 6]
    expected = [sum(weights[row] * values[2*row+col] for row in range(4)) % 2130706433
                for col in range(2)]
    assert list(map(int, result['result'])) == expected
    assert result['remaining'] == '0' and result['columns'] == '2'
    # Interpolating the pointwise product is not multiplying interpolated factors.
    product_mle = sum(weights[r] * values[2*r] * values[2*r+1] for r in range(4)) % 2130706433
    assert product_mle != expected[0] * expected[1] % 2130706433
    zero = entry.run('zero-variables', {'data': ['4', '9'], 'dimensions': '0', 'width': '2', 'point': []})
    assert zero['result'] == ['4', '9']
    partial = entry.run('prefix', {'data': list(map(str, values)), 'dimensions': '2', 'width': '2', 'point': ['2']})
    assert partial['result'] == ['13', '20', '23', '29'] and partial['remaining'] == '1'
    for name, data, dimensions, width, point in [
        ('odd', ['1', '2', '3'], '1', '1', []),
        ('wrong-width', ['1', '2', '3', '4'], '2', '2', []),
        ('empty', [], '0', '1', []),
        ('zero-width', [], '0', '0', []),
        ('oversized-dimension', ['1'], '64', '1', []),
        ('too-many-coordinates', ['1'], '0', '1', ['2']),
    ]:
        entry.run(name, {'data': data, 'dimensions': dimensions, 'width': width, 'point': point}, refuses=True)


@pytest.mark.parametrize('flags', [(), ('--no-simplify',)])
def test_table_shape_predicate_returns_false(toolchain, journal, directory, flags):
    source = '''module sample;
      use zkc::vector::{Vector}; use zkc::multilinear as mle;
      domain F=field("koala-bear");
      protocol Run roles(P)(values:Vector<F>@P,dimensions:index@P,columns:index@P)
          ->(valid:bool@P){return mle::has_shape(values,dimensions,columns);}
      run Demo=Run;
    '''
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    for name, values, dimensions, columns, valid in [
        ('valid', ['1', '2'], '1', '1', True),
        ('empty', [], '0', '1', False),
        ('zero-columns', [], '0', '0', False),
        ('oversized-dimension', ['1'], '64', '1', False),
    ]:
        result = entry.run(name, {'values': values, 'dimensions': dimensions, 'columns': columns})
        assert result['valid'] is valid


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_coset_word_domain_and_fold(toolchain, journal, directory, flags):
    source = '''module sample;
    use zkc::vector as vec;
    use zkc::coset as coset;
    use zkc::polynomial as poly;
    domain F=field("koala-bear");
    fn check(coefficients:vec::Vector<F>,shift:F,size:index,beta:F){
      let polynomial=poly::from_coefficients(coefficients);
      let input=coset::evaluate_coset(polynomial,shift,size);
      let admitted=coset::word(coset::values(input),coset::offset(input));
      let roundtrip=coset::interpolate(admitted);
      let folded=coset::fold(admitted,beta);
      let wrong=coset::interpolate(coset::word(coset::values(input),shift+1));
      let reordered=coset::interpolate(coset::word(vec::rotate(coset::values(input),1),shift));
      return (poly::evaluate(roundtrip,7),coset::values(folded),coset::offset(folded),
              poly::evaluate(wrong,7),poly::evaluate(reordered,7));
    }
    protocol Run roles(P)(coefficients:vec::Vector<F>@P,shift:F@P,size:index@P,beta:F@P)
      ->(value:F@P,folded:vec::Vector<F>@P,shift:F@P,wrong:F@P,reordered:F@P){
      let result=check(coefficients,shift,size,beta);
      return(value=result.0,folded=result.1,shift=result.2,wrong=result.3,reordered=result.4);
    }run Demo=Run;
    '''
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    args = {'coefficients': ['1', '2', '3'], 'shift': '3', 'size': '4', 'beta': '5'}
    result = entry.run('coset', args)
    assert result['value'] == '162'
    assert result['shift'] == '9'
    assert result['folded'] == ['38', str(2130706433 - 16)]
    assert result['wrong'] != result['value'] and result['reordered'] != result['value']
    for name, changes in [('zero-shift', {'shift': '0'}), ('non-two-adic', {'size': '3'}), ('empty', {'size': '0'})]:
        entry.run(name, args | changes, refuses=True)


@pytest.mark.parametrize('view,construction', [
    ('mle::Table<F>', 'mle::Table<F>{entries:values,dimensions:0,columns:1}'),
    ('coset::Word<F>', 'coset::Word<F>{data:values,shift:1}'),
])
@pytest.mark.parametrize('boundary', ['construct', 'entry', 'message'])
def test_view_constructor_authority(toolchain, journal, directory, view, construction, boundary):
    declarations = '''module sample;
      use zkc::vector::{Vector};
      use zkc::multilinear as mle;
      use zkc::coset as coset;
      domain F=field("koala-bear");
    '''
    if boundary == 'construct':
        body = f'fn bypass(values:Vector<F>)->{view}{{return {construction};}}'
    elif boundary == 'entry':
        body = f'protocol Run roles(P)(value:{view}@P)->(result:{view}@P){{return value;}} run Demo=Run;'
    else:
        make = 'mle::table(values,0,1)' if view.startswith('mle') else 'coset::word(values,1)'
        body = f'''protocol Run roles(P,V)(values:Vector<F>@P)->(result:{view}@V){{
          let value={make};let received=send P -> V(value);return received;
        }} run Demo=Run;'''
    path = directory / 'private.zkc'
    path.write_text(declarations + body)
    report = journal.json([toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
                           f'--module=sample={path}', *MODULES,
                           *(['sample::Demo'] if boundary == 'entry' else [])], refuses='source-compilation')
    code = 'source.private' if boundary == 'construct' else 'source.ingress'
    assert report['diagnostics'].startswith(code + ':'), report


@pytest.mark.parametrize('operation,inputs', [
    ('coset::values(coset::evaluate_coset(poly::from_coefficients(data),shift,size))',
     [{'data': ['1'], 'shift': '0', 'size': '4'},
      {'data': ['1'], 'shift': '1', 'size': '0'}]),
    ('coset::values(coset::word(data,shift))',
     [{'data': [], 'shift': '1', 'size': '0'}]),
    ('coset::values(coset::fold(coset::word(data,shift),1))',
     [{'data': ['1'], 'shift': '1', 'size': '1'}]),
])
def test_coset_constructors_own_admission(toolchain, journal, directory, operation, inputs):
    source = f'''module sample;
      use zkc::coset as coset; use zkc::vector::{{Vector}};
      use zkc::polynomial as poly; domain F=field("koala-bear");
      protocol Run roles(P)(data:Vector<F>@P,shift:F@P,size:index@P)->(value:Vector<F>@P){{
        return {operation};
      }} run Demo=Run;
    '''
    entry = Entry(toolchain, journal, directory, source, MODULES)
    for i, values in enumerate(inputs):
        entry.run(f'invalid-{i}', values, refuses='entry-run-incomplete')
