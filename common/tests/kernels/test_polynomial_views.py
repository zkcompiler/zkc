"""Checked roots, evaluations and opening descriptors against plain arithmetic."""
import pytest

from entry import Entry
from source_modules import library_modules

R = 52435875175126190479447740508185965837690552500527637822603658699938581184513
MODULES = library_modules('commitments/kzg')
SOURCE = '''module sample;
use zkc::vector::{Vector};
use zkc::evaluation_domain as evaluation;
use kzg as kzg;
domain F=field("bls12-381.fr");
protocol Run roles(P)(roots:Vector<F>@P,data:Vector<F>@P,count:index@P,
    generator:F@P,mode:index@P,z:F@P)->(points:Vector<F>@P,y:F@P,q:Vector<F>@P) {
  let unity = SELECT_DOMAIN;
  let input = evaluation::evaluations(unity,data);
  let (q,y) = kzg::quotient(input,z);
  require y == kzg::evaluate(input,z);
  return (points=evaluation::points(unity),y=y,q=q);
}
run Demo=Run;
'''


def source(mode):
    expression = ['evaluation::checked_roots(roots)',
                  'evaluation::two_adic(count,generator)',
                  'evaluation::two_adic_bit_reversed(count,generator)'][mode]
    return SOURCE.replace('SELECT_DOMAIN', expression)


def polynomial(coefficients, x):
    return sum(value * pow(x, i, R) for i, value in enumerate(coefficients)) % R


@pytest.mark.parametrize('flags', [(), ('--no-simplify',), ('--release-storage',),
                                  ('--no-simplify', '--release-storage')])
@pytest.mark.parametrize('selection', ['if', 'match'])
def test_checked_views_and_their_fields_share_control_captures(toolchain, journal, directory, flags, selection):
    text = '''module sample;
    use zkc::vector as vector;
    use zkc::vector::{Vector};
    use zkc::evaluation_domain as evaluation;
    use zkc::evaluation_domain::{EvaluationDomain};
    domain F=field("bls12-381.fr");
    fn choose(input:EvaluationDomain<F>, flag:bool)->EvaluationDomain<F> {
      let roots=evaluation::points(input);
      return if flag { input } else { evaluation::checked_roots(roots) };
    }
    fn count(input:EvaluationDomain<F>, rounds:index)->index {
      let roots=evaluation::points(input);
      let mut result:index=0;
      for _ in 0..rounds {
        result=result+evaluation::size(input)+vector::length(roots);
      }
      return result;
    }
    protocol Run roles(P)(roots:Vector<F>@P,flag:bool@P,rounds:index@P)
        ->(points:Vector<F>@P,total:index@P) {
      let input=choose(evaluation::checked_roots(roots),flag);
      return (points=evaluation::points(input),total=count(input,rounds));
    }
    run Demo=Run;
    '''
    if selection == 'match':
        text = text.replace('fn choose(', 'enum Choice{Original(),Readmitted()}\nfn choose(')
        text = text.replace('return if flag { input } else { evaluation::checked_roots(roots) };', '''
          let choice=if flag { Choice::Original() } else { Choice::Readmitted() };
          return match choice {
            Original()=>{input}, Readmitted()=>{evaluation::checked_roots(roots)}
          };''')
    entry = Entry(toolchain, journal, directory, text, (*flags, *MODULES))
    roots = ['1', str(R-1)]
    for flag in (False, True):
        for rounds in (0, 2):
            assert entry.run(f'{flag}-{rounds}', {
                'roots': roots, 'flag': flag, 'rounds': str(rounds)}) == {
                    'points': roots, 'total': str(4*rounds)}


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_kzg_quotient_derives_its_value_and_preserves_domain_order(toolchain, journal, directory, flags):
    entries = {}
    for mode in range(3):
        child = directory / f'mode-{mode}'
        child.mkdir()
        entries[mode] = Entry(toolchain, journal, child, source(mode), (*flags, *MODULES))
    cases = [(1, 1, 0, False), (2, R-1, 1, False),
             (4, pow(7, (R-1)//4, R), 2, False),
             (8, pow(7, (R-1)//8, R), 0, True),
             (3, pow(7, (R-1)//3, R), 0, True)]
    for number, (count, generator, mode, permute) in enumerate(cases):
        points = [pow(generator, i, R) for i in range(count)]
        if mode == 2:
            bits = (count-1).bit_length()
            points = [points[int(f'{i:0{bits}b}'[::-1], 2)] for i in range(count)]
        elif permute:
            points = points[1:] + points[:1]
        coefficients = [3, 5, 2, 9][:count]
        data = [polynomial(coefficients, x) for x in points]
        for label, z in [('outside', 13), ('inside', points[-1])]:
            expected_y = polynomial(coefficients, z)
            expected_q = [(value-expected_y) * pow((x-z) % R, -1, R) % R
                          if x != z else
                          sum(i * c * pow(z, i-1, R) for i, c in enumerate(coefficients) if i) % R
                          for x, value in zip(points, data)]
            result = entries[mode].run(f'{number}-{label}', {
                'roots': list(map(str, points)), 'data': list(map(str, data)),
                'count': str(count), 'generator': str(generator), 'mode': str(mode), 'z': str(z)})
            assert list(map(int, result['points'])) == points
            assert int(result['y']) == expected_y
            assert list(map(int, result['q'])) == expected_q


@pytest.mark.parametrize('change', [
    {'roots': [], 'data': []},
    {'roots': ['1', '1'], 'data': ['2', '3']},
    {'roots': ['1', '2'], 'data': ['2', '3']},
    {'data': []},
    {'mode': '1', 'count': '0', 'data': []},
    {'mode': '1', 'count': '3', 'data': ['1', '2', '3']},
    {'mode': '1', 'count': '4', 'generator': str(R-1), 'data': ['1']*4},
    {'mode': '1', 'count': '1', 'generator': '2'},
    {'mode': '2', 'count': '4', 'generator': '0', 'data': ['1']*4},
])
def test_invalid_domains_and_evaluation_extents_stop(toolchain, journal, directory, change):
    entry = Entry(toolchain, journal, directory, source(int(change.get('mode', '0'))), MODULES)
    values = {'roots': ['1'], 'data': ['2'], 'count': '1', 'generator': '1', 'mode': '0', 'z': '3'}
    entry.run('invalid', values | change, refuses='entry-run-incomplete')


@pytest.mark.parametrize('view,construction', [
    ('evaluation::EvaluationDomain<F>', 'evaluation::EvaluationDomain<F>{points:values}'),
    ('evaluation::Evaluations<F>', 'evaluation::Evaluations<F>{unity:evaluation::checked_roots(values),values:values}'),
    ('claims::OpeningClaims<F>', 'claims::OpeningClaims<F>{selected:indices::empty(),offsets:indices::empty(),claimed:values}'),
    ('coset::CosetDomain<F>', 'coset::CosetDomain<F>{shift:3,size:4}'),
    ('coset::ColumnBatch<F>', 'coset::ColumnBatch<F>{geometry:coset::coset_domain<F>(3,4),width:1,data:values}'),
    ('opening::BoundOpenings<F>', 'opening::BoundOpenings<F>{geometry:coset::coset_domain<F>(3,4),width:1,selected:indices::empty(),claimed:values,points:values}'),
    ('opening::VectorAccumulator<F>', 'opening::VectorAccumulator<F>{geometry:coset::coset_domain<F>(3,4),weights:opening::GeometricWeights<F>{ratio:1,next:1},values:values}'),
    ('opening::QueryRow<F>', 'opening::QueryRow<F>{geometry:coset::coset_domain<F>(3,4),width:1,position:0,values:values}'),
    ('opening::ScalarAccumulator<F>', 'opening::ScalarAccumulator<F>{geometry:coset::coset_domain<F>(3,4),position:0,weights:opening::GeometricWeights<F>{ratio:1,next:1},value:0}'),
])
@pytest.mark.parametrize('boundary', ['construct', 'project', 'entry', 'message'])
def test_checked_polynomial_views_require_owner_admission(toolchain, journal, directory, view, construction, boundary):
    source = '''module sample; use zkc::vector::{Vector}; use zkc::indices as indices;
      use zkc::evaluation_domain as evaluation; use zkc::opening_claims as claims;
      use zkc::coset as coset; use zkc::opening as opening;
      domain F=field("koala-bear");'''
    if boundary == 'construct':
        source += f'fn bypass(values:Vector<F>)->{view}{{return {construction};}}'
    elif boundary == 'project':
        field = {'evaluation::EvaluationDomain<F>': 'points',
                 'evaluation::Evaluations<F>': 'values', 'claims::OpeningClaims<F>': 'claimed',
                 'coset::CosetDomain<F>': 'shift', 'coset::ColumnBatch<F>': 'data',
                 'opening::BoundOpenings<F>': 'points', 'opening::VectorAccumulator<F>': 'values',
                 'opening::QueryRow<F>': 'values', 'opening::ScalarAccumulator<F>': 'value'}[view]
        source += f'fn bypass(value:{view}){{return value.{field};}}'
    elif boundary == 'entry':
        source += f'protocol Run roles(P)(value:{view}@P)->(result:{view}@P){{return value;}}run Demo=Run;'
    else:
        make = {'evaluation::EvaluationDomain<F>': 'evaluation::checked_roots(values)',
                'evaluation::Evaluations<F>': 'evaluation::evaluations(evaluation::checked_roots(values),values)',
                'claims::OpeningClaims<F>': 'claims::checked(indices::empty(),indices::empty(),values)',
                'coset::CosetDomain<F>': 'coset::coset_domain<F>(3,4)',
                'coset::ColumnBatch<F>': 'coset::column_batch(coset::coset_domain<F>(3,4),1,values)',
                'opening::BoundOpenings<F>': 'opening::bind_openings(coset::coset_domain<F>(3,4),1,2,5,claims::checked(indices::empty(),indices::empty(),values))',
                'opening::VectorAccumulator<F>': 'opening::vector_accumulator(coset::coset_domain<F>(3,4),7,values,1)',
                'opening::QueryRow<F>': 'opening::query_row(coset::coset_domain<F>(3,4),1,0,values)',
                'opening::ScalarAccumulator<F>': 'opening::scalar_accumulator(coset::coset_domain<F>(3,4),0,7,0,1)'}[view]
        source += f'''protocol Run roles(P,V)(values:Vector<F>@P)->(accepted:bool@V){{
          let input @P={make};let received=send P->V(input);return true;}}run Demo=Run;'''
    path = directory / 'private.zkc'
    path.write_text(source)
    report = journal.json([toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
                           f'--module=sample={path}', *MODULES,
                           *(['sample::Demo'] if boundary == 'entry' else [])], refuses='source-compilation')
    assert report['diagnostics'].startswith(('source.private' if boundary in ('construct', 'project') else 'source.ingress') + ':')


def test_opening_claims_preserve_repeated_order_and_validate_bounds(toolchain, journal, directory):
    source = '''module sample;use zkc::vector::{Vector};use zkc::indices::{Indices};
    use zkc::opening_claims as claims;domain F=field("koala-bear");
    protocol Run roles(P)(selected:Indices@P,offsets:Indices@P,data:Vector<F>@P,width:index@P,height:index@P)
      ->(columns:Indices@P,rotations:Indices@P,values:Vector<F>@P){
      let admitted=claims::within(claims::checked(selected,offsets,data),width,height);
      return(columns=claims::columns(admitted),rotations=claims::rotations(admitted),values=claims::values(admitted));
    }run Demo=Run;'''
    entry = Entry(toolchain, journal, directory, source, MODULES)
    inputs = {'selected': ['1','0','1'], 'offsets': ['2','0','2'], 'data': ['7','11','13'], 'width':'2','height':'4'}
    result = entry.run('ordered-duplicates', inputs)
    assert result == {'columns': inputs['selected'], 'rotations': inputs['offsets'], 'values': inputs['data']}
    for number, change in enumerate([{'offsets':['2']}, {'data':[]}, {'width':'1'},
                                     {'height':'2'}, {'height':'0'}]):
        entry.run(f'invalid-{number}', inputs | change, refuses='entry-run-incomplete')


@pytest.mark.parametrize('operation', ['columns', 'row'])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_deep_openings_check_bounds_and_denominators(toolchain, journal, directory, operation, flags):
    source = '''module sample;
    use zkc::vector as vector;use zkc::vector::{Vector};use zkc::indices::{Indices};
    use zkc::opening as opening;use zkc::opening_claims as claims;use zkc::coset as coset;
    domain F=field("koala-bear");
    protocol Run roles(P)(columns:Vector<F>@P,row:Vector<F>@P,selected:Indices@P,
      offsets:Indices@P,data:Vector<F>@P,height:index@P,size:index@P,zeta:F@P,position:index@P)
      ->(result:Vector<F>@P,weight:F@P,points:Vector<F>@P){
      let geometry=coset::coset_domain<F>(3,size);
      let input=opening::bind_openings(geometry,2,height,zeta,claims::checked(selected,offsets,data));
      let reduced=REDUCE;
      return(result=RESULT,weight=WEIGHT,points=coset::points<F>(3,size));
    }run Demo=Run;'''
    if operation == 'columns':
        source = source.replace('REDUCE', '''opening::deep_columns(coset::column_batch(geometry,2,columns),input,
          opening::vector_accumulator(geometry,7,vector::fill<F>(0,size),1))''').replace('RESULT', 'opening::vector_values(reduced)').replace('WEIGHT', 'opening::vector_weight(reduced)')
    else:
        source = source.replace('REDUCE', 'opening::deep_row(opening::query_row(geometry,2,position,row),input,opening::scalar_accumulator(geometry,position,7,0,1))')
        source = source.replace('RESULT', 'vector::fill(opening::scalar_value(reduced),size)').replace('WEIGHT', 'opening::scalar_weight(reduced)')
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    inputs = {'columns': ['11']*4 + ['13']*4, 'row': ['11','13'],
              'selected': ['1','0','1'], 'offsets': ['1','0','1'], 'data': ['7','9','7'],
              'height': '2', 'size': '4', 'zeta': '5', 'position': '1'}
    output = entry.run('ordered-duplicates', inputs)
    modulus = 2130706433

    def expected(x):
        return sum(pow(7, i, modulus) * (int(inputs['row'][int(column)]) - int(value)) *
                   pow((x - 5 * (-1 if int(rotation) else 1)) % modulus, -1, modulus)
                   for i, (column, rotation, value) in enumerate(zip(
                       inputs['selected'], inputs['offsets'], inputs['data']))) % modulus

    points = [int(value) for value in output['points']]
    assert [int(value) for value in output['result']] == [
        expected(point if operation == 'columns' else points[1]) for point in points]
    assert output['weight'] == '343'
    empty = entry.run('empty', inputs | {'selected': [], 'offsets': [], 'data': []})
    assert empty['result'] == ['0']*4 and empty['weight'] == '1'
    changes = [{'selected': ['1','0','2']}, {'offsets': ['1','0','2']}, {'data': ['7']},
               {'height': '0'}, {'selected': [], 'offsets': [], 'data': [], 'height': '0'}]
    if operation == 'columns':
        # A claim on the evaluation coset must refuse its zero denominator.
        changes += [{'size': '0'}, {'columns': ['11']*7},
                    {'selected': ['0'], 'offsets': ['0'], 'data': ['11'], 'zeta': '3'}]
    else:
        changes += [{'row': ['11']}, {'position': '4'}, {'zeta': '3'}]
    for number, change in enumerate(changes):
        entry.run(f'invalid-{number}', inputs | change, refuses='entry-run-incomplete')
