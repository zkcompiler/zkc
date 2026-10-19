"""Opening joins bind actual geometry and preserve ordered weight continuation."""
import pytest

from entry import Entry
from source_modules import library_modules

MODULES = library_modules('core/polynomial')
SOURCE = '''module sample;
use zkc::vector as vector;use zkc::vector::{Vector};
use zkc::indices as indices;use zkc::opening as opening;use zkc::coset as coset;
domain F=field("koala-bear");
fn selected_columns(is_empty:bool)->indices::Indices {
 return if is_empty { indices::empty() } else { indices::append(indices::empty(),0) };
}
fn claimed_values(is_empty:bool)->Vector<F> {
 return if is_empty { vector::empty<F>() } else { vector::fill<F>(2,1) };
}
protocol Run roles(P)(shift:F@P,bound_shift:F@P,state_shift:F@P,
 size:index@P,bound_size:index@P,state_size:index@P,width:index@P,bound_width:index@P,
 position:index@P,state_position:index@P,data:Vector<F>@P,initial:Vector<F>@P,
 height:index@P,zeta:F@P,empty:bool@P)
 ->(result:Vector<F>@P,weight:F@P){
 let geometry=coset::coset_domain(shift,size);
 let bound_geometry=coset::coset_domain(bound_shift,bound_size);
 let state_geometry=coset::coset_domain(state_shift,state_size);
 let selected=selected_columns(empty);
 let values=claimed_values(empty);
 let descriptors=zkc::opening_claims::checked(selected,selected,values);
 let bound=opening::bind_openings(bound_geometry,bound_width,height,zeta,descriptors);
 let first=REDUCE;
 // Reconstructing the same context and threading the result continues weights.
 let rebound=opening::bind_openings(coset::coset_domain(bound_shift,bound_size),
   bound_width,height,zeta,descriptors);
 let next=CONTINUE;
 return(result=RESULT,weight=WEIGHT);
}run Demo=Run;
'''


@pytest.mark.parametrize('operation', ['columns', 'row'])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_context_joins_and_weight_continuation(toolchain, journal, directory, operation, flags):
    if operation == 'columns':
        reduce = ('opening::deep_columns(coset::column_batch(geometry,width,data),bound,'
                  'opening::vector_accumulator(state_geometry,7,initial,5))')
        continuation = 'opening::deep_columns(coset::column_batch(geometry,width,data),rebound,first)'
        result, weight = 'opening::vector_values(next)', 'opening::vector_weight(next)'
    else:
        reduce = ('opening::deep_row(opening::query_row(geometry,width,position,data),bound,'
                  'opening::scalar_accumulator(state_geometry,state_position,7,3,5))')
        continuation = 'opening::deep_row(opening::query_row(geometry,width,position,data),rebound,first)'
        result, weight = 'vector::fill(opening::scalar_value(next),size)', 'opening::scalar_weight(next)'
    source = SOURCE.replace('REDUCE', reduce).replace('CONTINUE', continuation)
    source = source.replace('RESULT', result).replace('WEIGHT', weight)
    entry = Entry(toolchain, journal, directory, source, (*MODULES, *flags))
    base = {'shift': '3', 'bound_shift': '3', 'state_shift': '3',
            'size': '4', 'bound_size': '4', 'state_size': '4',
            'width': '1', 'bound_width': '1', 'position': '0', 'state_position': '0',
            'data': ['11'] * (4 if operation == 'columns' else 1), 'initial': ['3']*4,
            'height': '2', 'zeta': '5', 'empty': False}
    output = entry.run('continued', base)
    p = 2130706433
    # Two occurrences of the same descriptor consume weights 5 and 35.
    root = pow(1791270792, (1 << 24)//4, p)
    points = [3*pow(root, i, p) % p for i in range(4)]
    expected = [(3 + 40*9*pow((x-5) % p, -1, p)) % p for x in points]
    assert output == {'result': list(map(str, expected if operation == 'columns' else [expected[0]]*4)),
                      'weight': '245'}
    assert entry.run('empty', base | {'empty': True}) == {'result': ['3']*4, 'weight': '5'}
    invalid = [{'bound_shift': '7'}, {'state_shift': '7'}, {'bound_size': '8'},
               {'state_size': '8'}, {'bound_width': '2'}, {'shift': '0'},
               {'size': '0'}, {'size': '3'}, {'size': str(1 << 25)},
               {'height': '0'}, {'height': '3'}, {'zeta': '3'}]
    if operation == 'columns':
        invalid += [{'width': str(1 << 63)}, {'initial': []}, {'data': ['11']}]
    else:
        invalid += [{'position': '4'}, {'state_position': '1'}, {'width': '2'}]
    for number, change in enumerate(invalid):
        entry.run(f'invalid-{number}', base | change, refuses='entry-run-incomplete')
    for number, change in enumerate([{'bound_shift': '7'}, {'bound_width': '2'}, {'height': '0'}]):
        entry.run(f'empty-invalid-{number}', base | {'empty': True} | change,
                  refuses='entry-run-incomplete')
