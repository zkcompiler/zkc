"""Checked collect–fold composition through source compilation and the Host."""

import importlib
import json
from pathlib import Path

import pytest

from entry import Entry, joint_artifact
from input_files import decimal_values
from octic_reference import P, add, mul
from test_total_callback_selection import compile_entry


PREFIX = '''module sample;
domain F=field("FIELD");
type Vector<E:Field>=builtin("vector",E);
domain fn elements<E:Field>(xs:Vector<E>)->domain<E>=domain("elements");
domain fn indices<E:Field>(xs:Vector<E>)->domain<index>=domain("indices");
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
math fn collect<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))->Vector<F>=finite("math.collect.vector");
math fn fold<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn at(xs:Vector<F>,i:index)->F where in_bounds(i,xs){return intrinsic<Vector<F>>("container.at",xs,i);}
'''

FLAGS = [(), ('--fuse-collect-fold',),
         ('--fuse-collect-fold', '--no-finite-bulk'),
         ('--fuse-collect-fold', '--no-simplify', '--release-storage')]


def assert_streamed(sites, flags):
    if '--fuse-collect-fold' in flags:
        # Input extent/access operations remain. No intermediate vector builder
        # or bulk producer may hide behind an absent append instruction.
        assert {name for name, count in sites.items()
                if count and name.startswith('vector.')} <= {'vector.length', 'vector.get'}
        assert not sites['numerical.map'], sites


@pytest.mark.parametrize('field', ['koala-bear', 'bls12-381.fr'])
@pytest.mark.parametrize('bulk', [False, True])
@pytest.mark.parametrize('form', ['total-collect-fold', 'total-fold'])
def test_benchmark_exercises_composition(toolchain, journal, directory, monkeypatch, field, bulk, form):
    # The timed workload must expose a single total mathematical unit. Ordinary
    # function call boundaries would test two separate kernels instead.
    monkeypatch.syspath_prepend(str(Path(__file__).resolve().parents[2] / 'benchmarks'))
    program = importlib.import_module('bench.programs').finite({
        'field': field, 'elements': 17, 'form': form})
    source = program.source.replace('module example;', 'module sample;')
    candidates = []
    for fused in (False, True):
        selected = directory / ('fused' if fused else 'default')
        selected.mkdir()
        flags = ([] if bulk else ['--no-finite-bulk']) + (['--fuse-collect-fold'] if fused else [])
        entry, sites = compile_entry(toolchain, journal, selected, source, flags)
        if form == 'total-collect-fold':
            if fused:
                assert_streamed(sites, flags)
            else:
                assert sites['numerical.map' if bulk else 'vector.append']
        assert entry.run(f'correct-{fused}', program.inputs[0]['P']) == {'accepted': True}
        assert entry.run(f'incorrect-{fused}', program.incorrect['P']) == {'accepted': False}
        package = json.loads(entry.package.read_text())
        candidates.append(json.loads(joint_artifact(package)['candidate']))
    if form == 'total-fold':
        assert candidates[0] == candidates[1], 'fusion must not change a direct fold'


@pytest.mark.parametrize('flags', FLAGS)
@pytest.mark.parametrize('indexed', [False, True], ids=['elements', 'indices'])
@pytest.mark.parametrize('extension', [False, True], ids=['base', 'extension'])
def test_ordered_multistate_composition(toolchain, journal, directory, flags, indexed, extension):
    # Nonassociative state update makes reordering, wrong seeds, and accidentally
    # using the original state instead of loop-carried state observable.
    source = PREFIX + '''
math fn work(xs:Vector<F>,first:F,second:F)->(F,F){
 let initial=(first,second);
 let ys=collect(elements(xs),fn(x)=>x*x+first);
 return fold(DOMAIN(ys),initial,fn((a,b),x)=>(b,a*b+ITEM));
}
protocol Work roles(P)(xs:Vector<F>@P,first:F@P,second:F@P)->(result:(F,F)@P){
 return work(xs,first,second);
}run Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    field = 'koala-bear' + ('.ext8-binomial3' if extension else '')
    source = source.replace('FIELD', field).replace('DOMAIN', 'indices' if indexed else 'elements')
    source = source.replace('ITEM', 'at(ys,x)' if indexed else 'x')
    entry, sites = compile_entry(toolchain, journal, directory, source, flags)
    assert_streamed(sites, flags)
    if extension:
        values = [[2, 1, 0, 0, 0, 0, 0, 3], [3, 0, 0, 0, 1, 0, 0, 1], [5, 2, 0, 0, 0, 0, 0, 0]]
        first, second = [7, 3, 0, 0, 0, 0, 0, 0], [11, 0, 1, 0, 0, 0, 0, 0]
        plus, times = add, mul
    else:
        values, first, second = [2, 3, 5], 7, 11
        plus, times = lambda a, b: (a+b) % P, lambda a, b: a*b % P
    for count in (0, 1, 3):
        a, b = first, second
        for value in values[:count]:
            item = plus(times(value, value), first)
            a, b = b, plus(times(a, b), item)
        assert entry.run(f'length-{count}', {'xs': values[:count], 'first': first, 'second': second}) == {
            'result': decimal_values([a, b])}


@pytest.mark.parametrize('flags', FLAGS)
def test_total_zip_preserves_both_items(toolchain, journal, directory, flags):
    source = PREFIX + '''
math fn work(xs:Vector<F>,seed:F)->F{
 let values=collect(zip(elements(xs),elements(xs)),fn((x,y))=>x*x+y);
 return fold(elements(values),seed,fn(s,x)=>s*s+x);
}
protocol Work roles(P)(xs:Vector<F>@P,seed:F@P)->(result:F@P){return work(xs,seed);}
run Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    entry, sites = compile_entry(toolchain, journal, directory,
                                 source.replace('FIELD', 'koala-bear'), flags)
    assert_streamed(sites, flags)
    assert entry.run('empty', {'xs': [], 'seed': 7}) == {'result': '7'}
    assert entry.run('values', {'xs': [2, 3], 'seed': 7}) == {'result': '3037'}


@pytest.mark.parametrize('flags', FLAGS)
def test_partial_zip_admission_and_empty_seed(toolchain, journal, directory, flags):
    # Independent extents use the fallible library form. Enabling total fusion
    # must retain the zip guard and its empty-domain behavior.
    source = '''module sample;
use zkc::vector as vec;
use zkc::sequence as seq;
use zkc::finite as finite;
use zkc::finite_domain::{zip};
domain F=field("koala-bear");
fn work(xs:vec::Vector<F>,ys:vec::Vector<F>,seed:F)->F{
 let values=finite::collect(zip(vec::elements(xs),vec::elements(ys)),fn((x,y))=>x*x);
 return finite::fold(seq::elements(values),seed,fn(s,x)=>s*s+x);
}
protocol Work roles(P)(xs:vec::Vector<F>@P,ys:vec::Vector<F>@P,seed:F@P)->(result:F@P){return work(xs,ys,seed);}
run Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    entry, sites = compile_entry(toolchain, journal, directory, source, flags)
    assert sites['sequence.append'], 'partial collect must retain materialization'
    assert entry.run('empty', {'xs': [], 'ys': [], 'seed': 7}) == {'result': '7'}
    assert entry.run('equal', {'xs': [2, 3], 'ys': [11, 13], 'seed': 7}) == {'result': '2818'}
    for label, xs, ys in [('left-empty', [], [2]), ('right-empty', [2], []),
                           ('different', [2, 3], [5])]:
        entry.run(label, {'xs': xs, 'ys': ys, 'seed': 7}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('flags', FLAGS)
def test_shared_collection_keeps_its_value(toolchain, journal, directory, flags):
    source = PREFIX + '''
math fn work(xs:Vector<F>,seed:F)->(Vector<F>,F){
 let ys=collect(elements(xs),fn(x)=>x*x+seed);
 let result=fold(elements(ys),seed,fn(s,x)=>s*s+x);
 return(ys,result);
}
protocol Work roles(P)(xs:Vector<F>@P,seed:F@P)->(result:(Vector<F>,F)@P){return work(xs,seed);}
run Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source.replace('FIELD', 'koala-bear'), flags)
    assert entry.run('empty', {'xs': [], 'seed': 7}) == {'result': [[], '7']}
    assert entry.run('shared', {'xs': [2, 3], 'seed': 7}) == {'result': [['11', '16'], '3616']}


@pytest.mark.parametrize('flags', FLAGS)
def test_nested_domain_failure_stays_conditional(toolchain, journal, directory, flags):
    source = PREFIX + '''
math fn work(xs:Vector<F>,limit:index,seed:F)->F{
 let values=collect(elements(xs),fn(x)=>fold(range(0,limit),x,fn(s,i)=>s+1));
 return fold(elements(values),seed,fn(s,x)=>s*s+x);
}
protocol Work roles(P)(xs:Vector<F>@P,limit:index@P,seed:F@P)->(result:F@P){return work(xs,limit,seed);}
run Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source.replace('FIELD', 'koala-bear'), flags)
    assert entry.run('inner-empty', {'xs': [2, 3], 'limit': 0, 'seed': 7}) == {'result': '2604'}
    huge = str(2**64-1)
    assert entry.run('outer-empty', {'xs': [], 'limit': huge, 'seed': 7}) == {'result': '7'}
    entry.run('entered-inner', {'xs': [2], 'limit': huge, 'seed': 7}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('fused', [False, True])
def test_standard_collection_and_mixed_state(toolchain, journal, directory, fused):
    source = '''module sample;
use zkc::vector as vec;
use zkc::sequence as seq;
use zkc::finite_math as total;
domain F=field("koala-bear");
math fn work(xs:vec::Vector<F>,seed:F)->(F,bool){
 let initial=(seed,false);
 let ys=total::collect(vec::elements(xs),fn(x)=>x*x);
 return total::fold(seq::elements(ys),initial,fn((s,b),x)=>(s+x,s==x));
}
protocol Work roles(P)(xs:vec::Vector<F>@P,seed:F@P)->(result:(F,bool)@P){return work(xs,seed);}
run Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    flags = ['--fuse-collect-fold'] if fused else []
    entry, sites = compile_entry(toolchain, journal, directory, source, flags)
    assert bool(sites['sequence.append']) is not fused
    assert entry.run('empty', {'xs': [], 'seed': 7}) == {'result': ['7', False]}
    assert entry.run('values', {'xs': [2, 3], 'seed': 7}) == {'result': ['20', False]}
    assert entry.run('equal', {'xs': [2], 'seed': 4}) == {'result': ['8', True]}
