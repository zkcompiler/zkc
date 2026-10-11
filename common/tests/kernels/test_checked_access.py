"""Public checked library access through source compilation and the common Host."""
from pathlib import Path

import pytest

from entry import Entry

ROOT = Path(__file__).resolve().parents[3]
MODULES = [f'--module=zkc::{name}={ROOT}/libraries/zkc/{name}.zkc'
           for name in ('vector', 'matrix', 'field_array', 'symbolic',
                        'finite', 'sequence', 'accumulation', 'curve')]


@pytest.mark.parametrize('field', ['bls12-381.fr', 'bn254.fr', 'ristretto255.scalar',
                                  'koala-bear', 'koala-bear.ext8-binomial3'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_matrix_library_checked_access(toolchain, journal, directory, field, flags):
    source = f'''module sample;
use zkc::matrix::{{Matrix}};
domain F=field("{field}");
fn access(m:Matrix<F>,row:index,column:index)->F {{
  return zkc::matrix::get(m,row,column);
}}
protocol Run roles(P)(m:Matrix<F>@P,row:index@P,column:index@P)->(result:F@P) {{
  return access(m,row,column);
}}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    extension = field == 'koala-bear.ext8-binomial3'
    coefficient = ['7', '2', '0', '0', '0', '0', '0', '1'] if extension else '7'
    zero = ['0'] * 8 if extension else '0'
    matrix = {'rows': '2', 'columns': '3', 'entries': [['0', '1', coefficient]]}
    inputs = {'m': matrix, 'row': '0', 'column': '1'}
    assert entry.run('present', inputs)['result'] == coefficient
    assert entry.run('absent', inputs | {'row': '1', 'column': '2'})['result'] == zero
    for name, row, column in [('row', '2', '0'), ('column', '0', '3'),
                              ('wide-row', str(2**32), '1'),
                              ('huge-column', '0', str(2**64 - 1))]:
        report = entry.run(name, inputs | {'row': row, 'column': column},
                           refuses='entry-run-incomplete')
        assert 'matrix-index' in str(report)
    for rows, columns in [(0, 0), (0, 3), (2, 0)]:
        report = entry.run(f'empty-{rows}-{columns}', {
            'm': {'rows': str(rows), 'columns': str(columns), 'entries': []},
            'row': '0', 'column': '0'}, refuses='entry-run-incomplete')
        assert 'matrix-index' in str(report)


@pytest.mark.parametrize('length', [0, 1, 4])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_field_array_library_checked_access(toolchain, journal, directory, length, flags):
    source = f'''module sample;
use zkc::vector::{{Vector}};
domain F=field("bls12-381.fr");
fn access(values:Vector<F>,position:index)->F {{
  let array=zkc::field_array::from_vector<F,{length}>(values);
  return zkc::field_array::get(array,position);
}}
protocol Run roles(P)(values:Vector<F>@P,position:index@P)->(result:F@P) {{
  return access(values,position);
}}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    values = [str(3 * i + 7) for i in range(length)]
    for index, expected in enumerate(values):
        assert entry.run(f'valid-{index}', {'values': values, 'position': str(index)})['result'] == expected
    for index in (length, 2**32, 2**64 - 1):
        report = entry.run(f'outside-{index}', {'values': values, 'position': str(index)},
                           refuses='entry-run-incomplete')
        assert 'field-array-index' in str(report)
    report = entry.run('wrong-length', {'values': values + ['99'], 'position': '0'},
                       refuses='entry-run-incomplete')
    assert 'field-array-length' in str(report)


def test_static_symbolic_array_feeds_ordinary_dynamic_access(toolchain, journal, directory):
    source = '''module sample;
domain F=field("bls12-381.fr");
fn access(a:F,b:F,position:index)->(F,F) {
  let array=zkc::symbolic::pack([a,b]);
  return (zkc::field_array::get(array,position),zkc::symbolic::get<F,2,1>(array));
}
protocol Run roles(P)(a:F@P,b:F@P,position:index@P)->(result:(F,F)@P) {
  return access(a,b,position);
}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, MODULES)
    assert entry.run('valid', {'a': '7', 'b': '11', 'position': '0'})['result'] == ['7', '11']
    report = entry.run('outside', {'a': '7', 'b': '11', 'position': '2'}, refuses='entry-run-incomplete')
    assert 'field-array-index' in str(report)
