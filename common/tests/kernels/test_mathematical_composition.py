"""Helper facts, checked ingress and pack projections through independent readers."""

import json

import pytest

from entry import Entry, joint_execution
from input_files import input_files
from source_modules import core_packages, library_modules

MODULES = library_modules(*core_packages())
PRELUDE = '''module sample;
use zkc::vector as vec;
use zkc::finite as finite;
use zkc::finite_math as total;
use zkc::finite_domain as domains;
use zkc::field_array as arrays;
use zkc::symbolic as symbolic;
domain F=field("bls12-381.fr");
'''


@pytest.mark.parametrize('flags', [(), ('--no-simplify',), ('--no-finite-bulk',)])
def test_constructed_helper_extents_reach_ssa_and_execution(toolchain, journal, directory, flags):
    source = PRELUDE + '''
math fn collect<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))
 ->vec::Vector<F>=finite("math.collect.vector");
math fn copy(xs:vec::Vector<F>)->vec::Vector<F>{return collect(vec::elements(xs),fn(x)=>x);}
math fn term(xs:vec::Vector<F>,i:index)->F where in_bounds(i,xs){return vec::at(copy(xs),i);}
math fn work(xs:vec::Vector<F>)->F{return total::sum(vec::indices(xs),fn(i)=>term(xs,i));}
protocol Run roles(P)(xs:vec::Vector<F>@P)->(value:F@P){return work(xs);}run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, (*MODULES, *flags))
    assert entry.run('nonempty', {'xs': ['2', '3', '5']})['value'] == '10'
    assert entry.run('empty', {'xs': []})['value'] == '0'


@pytest.mark.parametrize('flags', [(), ('--no-simplify',)])
def test_checked_static_conversion_precedes_total_consumer(toolchain, journal, directory, flags):
    source = PRELUDE + '''
math fn last(values:arrays::Array<F,3>)->F{return symbolic::get<F,3,2>(values);}
protocol Run roles(P)(xs:vec::Vector<F>@P)->(value:F@P){
 let fixed=arrays::from_vector<F,3>(xs);return last(fixed);
}run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, (*MODULES, *flags))
    assert entry.run('valid', {'xs': ['2', '3', '5']})['value'] == '5'
    for count in (0, 2, 4):
        entry.run(f'wrong-{count}', {'xs': ['7'] * count}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('nested', [False, True])
def test_pack_callbacks_preserve_values_guards_and_bounded_work(toolchain, journal, directory, nested):
    body = ('''let a=symbolic::pack<F,2>([pair.0,pair.0]);
 return total::sum(arrays::elements(a),fn(x)=>x*pair.1);''' if nested else '''
 let a=symbolic::pack<F,2>([pair.0,pair.1]);
 return symbolic::get<F,2,0>(a)*symbolic::get<F,2,1>(a);''')
    source = PRELUDE + f'math fn product(pair:(F,F))->F{{{body}}}' + '''
protocol Run roles(P)(xs:vec::Vector<F>@P,ys:vec::Vector<F>@P)->(value:F@P){
 return finite::sum(domains::zip(xs,ys),fn(pair)=>product(pair));
}run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    counters = []
    for name, flags in [('default', ()), ('ordered', ('--no-finite-bulk',)),
                        ('plain', ('--no-simplify',))]:
        folder = directory / name
        folder.mkdir()
        entry = Entry(toolchain, journal, folder, source, (*MODULES, *flags))
        assert entry.run('small', {'xs': ['2', '3'], 'ys': ['5', '7']})['value'] == str(62 if nested else 31)
        assert entry.run('empty', {'xs': [], 'ys': []})['value'] == '0'
        entry.run('strict-empty', {'xs': [], 'ys': ['1']}, refuses='entry-host-run-failed')
        entry.run('strict-nonempty', {'xs': ['1', '2'], 'ys': ['1']}, refuses='entry-host-run-failed')
        request = input_files(journal, f'{name}-large', package=entry.package, arguments={'inputs': {'P': {'xs': ['2'] * 64, 'ys': ['3'] * 64}}})
        output = folder / 'large.json'
        report = journal.json([toolchain.runtime, '--json', 'run', f'--package={entry.package}',
                               f'--sha256={entry.pin}', *request, f'--results={output}'])
        assert json.loads(output.read_text())['value']['P']['value'] == str(768 if nested else 384)
        counters.append(joint_execution(report)['roles'][0]['usage'])
    if not nested:
        for optimized in (counters[0], counters[2]):
            assert optimized['logical_bytes'] < counters[1]['logical_bytes']
            assert optimized['total_value_bytes'] < counters[1]['total_value_bytes']
