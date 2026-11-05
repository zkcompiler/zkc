"""Public finite libraries through source compilation and native execution."""
from pathlib import Path
import json

import pytest

from entry import Entry, joint_execution
from source_modules import core_packages, library_modules

ROOT = Path(__file__).resolve().parents[3]
MODULES = library_modules(*core_packages())


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk']])
@pytest.mark.parametrize('field', ['koala-bear', 'bls12-381.fr'])
def test_neutral_pointwise_sums_preserve_the_seed(toolchain, journal, directory, flags, field):
    source = f'''module sample;
use zkc::vector::{{Vector}};
use zkc::finite as finite;
domain F=field("{field}");
fn work(xs:Vector<F>,seed:F)->(F,F,F,F){{
 let a=finite::fold(xs,seed,fn(s,x)=>s+0*1);
 let b=finite::fold(xs,seed,fn(s,x)=>s+1*0);
 let c=finite::fold(xs,seed,fn(s,x)=>s+(0+0));
 let d=finite::fold(xs,seed,fn(s,x)=>s+(0*1+1*0));
 return(a,b,c,d);
}}
protocol Run roles(P)(xs:Vector<F>@P,seed:F@P)->(result:(F,F,F,F)@P){{return work(xs,seed);}}
entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    for n in (0, 3):
        assert entry.run(f'rows-{n}', {'xs': ['2']*n, 'seed': '7'})['result'] == ['7']*4


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk']])
def test_pointwise_sums_preserve_seeds_cardinality_and_captures(
    toolchain, journal, directory, flags,
):
    source = '''module sample;
use zkc::vector::{Vector,indexing []};
use zkc::finite as finite;
use zkc::finite_math as total;
use zkc::finite_domain as domains;
domain F=field("koala-bear");
math fn indexed_sum(xs:Vector<F>)->F{
 return total::sum(zkc::vector::indices(xs),fn(i)=>xs[i]*xs[i]+xs[i]);
}
fn work(xs:Vector<F>,unused:Vector<F>,seed:F,scale:F)->(F,F,F,F){
 let rows=domains::zip(xs,unused);
 let polynomial=finite::fold(rows,seed,fn(state,(x,_))=>state+(x*x+x));
 let uniform=finite::fold(rows,seed,fn(state,_)=>state+scale*scale);
 let indexed=indexed_sum(xs);
 let captured=finite::sum(rows,fn((x,_))=>(x-scale)*(x+scale)+scale);
 return(polynomial,uniform,indexed,captured);
}
protocol Run roles(P)(xs:Vector<F>@P,unused:Vector<F>@P,seed:F@P,scale:F@P)
 ->(result:(F,F,F,F)@P){return work(xs,unused,seed,scale);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    modulus = 2**31 - 2**24 + 1
    for n in (0, 1, 17):
        xs = [(i*73+modulus-1) % modulus for i in range(n)]
        seed, scale = modulus-7, modulus-3
        polynomial = sum(x*x+x for x in xs)
        expected = [seed+polynomial, seed+n*scale*scale, polynomial,
                    sum((x-scale)*(x+scale)+scale for x in xs)]
        inputs = {'xs': list(map(str, xs)), 'unused': ['9']*n,
                  'seed': str(seed), 'scale': str(scale)}
        assert entry.run(f'rows-{n}', inputs)['result'] == [str(x % modulus) for x in expected]
        iterations = joint_execution(json.loads(journal.last.stdout))['roles'][0]['usage']['iterations']
        assert iterations == (4*n if '--no-finite-bulk' in flags else 0)
        refused = entry.run(f'mismatched-{n}', inputs | {'unused': ['9']*(n+1)},
                            refuses='entry-host-run-failed')
        assert 'rejected:require' in json.dumps(refused)


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk']])
def test_pointwise_reduction_keeps_partial_and_recurrent_bodies_ordered(
    toolchain, journal, directory, flags,
):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::finite as finite;
domain F=field("koala-bear");
fn inverse(x:F)->F=primitive("field.inverse");
fn work(xs:Vector<F>,seed:F,enabled:bool)->(F,F){
 let recurrent=finite::fold(xs,seed,fn(state,x)=>state+(state*x+x));
 let partial=finite::fold(xs,seed,fn(state,x)=>{
   let unused=inverse(x);
   require enabled;
   state+(x*x+x)
 });
 return(recurrent,partial);
}
protocol Run roles(P)(xs:Vector<F>@P,seed:F@P,enabled:bool@P)
 ->(result:(F,F)@P){return work(xs,seed,enabled);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('empty', {'xs': [], 'seed': '7', 'enabled': False})['result'] == ['7', '7']
    assert entry.run('values', {'xs': ['2', '3'], 'seed': '7', 'enabled': True})['result'] == ['95', '25']
    report = json.loads(journal.last.stdout)
    assert joint_execution(report)['roles'][0]['usage']['iterations'] == 4
    inverse = entry.run('unused-partial', {'xs': ['0'], 'seed': '7', 'enabled': False},
                        refuses='entry-host-run-failed')
    assert 'refused:zero-inverse' in json.dumps(inverse)
    stopped = entry.run('explicit-stop', {'xs': ['1'], 'seed': '7', 'enabled': False},
                        refuses='entry-host-run-failed')
    assert joint_execution(stopped)['roles'][0]['after'][1]['cause'][0] == 'explicit'


@pytest.mark.parametrize('mode,module', [('fn', 'finite'), ('math fn', 'finite_math')])
@pytest.mark.parametrize('bulk', [True, False])
def test_pointwise_sum_dead_total_state_work_has_checked_realizations(
    toolchain, journal, directory, mode, module, bulk,
):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::FINITE_MODULE as finite;
domain F=field("koala-bear");
MODE work(xs:Vector<F>,seed:F)->F{
 return finite::fold(xs,seed,fn(state,x)=>{
   let unused=state*state;
   state+(x*x+x)
 });
}
protocol Run roles(P)(xs:Vector<F>@P,seed:F@P)->(result:F@P){return work(xs,seed);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''.replace('FINITE_MODULE', module).replace('MODE', mode)
    flags = [] if bulk else ['--no-finite-bulk']
    entry = Entry(toolchain, journal, directory, source, [*MODULES, '--no-simplify', *flags])
    assert entry.run('values', {'xs': ['2', '3'], 'seed': '7'})['result'] == '25'
    iterations = joint_execution(json.loads(journal.last.stdout))['roles'][0]['usage']['iterations']
    # The checked bulk recipe may discard total dead work in either mode.
    # The adjacent partial-work test retains unused inverses and explicit stops.
    assert iterations == (0 if bulk else 2)


def test_pointwise_sum_broadcast_uses_result_field_and_index_domain(
    toolchain, journal, directory,
):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::finite_math as finite;
domain K=field("koala-bear");
domain F=field("bls12-381.fr");
math fn work(xs:Vector<K>,seed:F,value:F)->F{
 return finite::fold(zkc::vector::indices(xs),seed,fn(state,_)=>state+value*value);
}
protocol Run roles(P)(xs:Vector<K>@P,seed:F@P,value:F@P)->(result:F@P){return work(xs,seed,value);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, '--no-simplify'])
    for n in (0, 3):
        assert entry.run(f'rows-{n}', {'xs': ['2']*n, 'seed': '7', 'value': '3'})['result'] == str(7+9*n)
        assert joint_execution(json.loads(journal.last.stdout))['roles'][0]['usage']['iterations'] == 0


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
@pytest.mark.parametrize('implicit', [False, True])
def test_named_finite_libraries_and_explicit_combiner(toolchain, journal, directory, flags, implicit):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::finite as finite;
use zkc::finite_domain as domains;
use zkc::accumulation::{Combiner};
domain F=field("koala-bear");
module Decimal:Combiner<F>{
 math fn identity()->F{return 0;}
 math fn combine(state:F,value:F)->F{return state*10+value;}
}
fn checked(x:F,ok:bool)->F{require ok;return x;}
fn work(xs:Vector<F>,ys:Vector<F>,enabled:bool)->(F,F,F,F,F,index){
 let paired=domains::zip(zkc::vector::elements(xs),zkc::vector::elements(ys));
 let dot=finite::sum(paired,fn((x,y))=>x*y);
 let ordered=finite::accumulate<_,F,Decimal>(zkc::vector::elements(xs),fn(x)=>x);
 let product=finite::product(zkc::vector::elements(xs),fn(x)=>x+1);
 let selected=finite::sum_where(zkc::vector::elements(xs),fn(x)=>enabled,fn(x)=>checked(x,enabled));
 let materialized=zkc::vector::reduce(zkc::vector::elements(xs),fn(x)=>x*x,fn(values)=>zkc::vector::sum(values));
 let pairs=finite::collect(domains::product(zkc::vector::elements(xs),zkc::vector::elements(ys)),fn(pair)=>pair);
 return(dot,ordered,product,selected,materialized,zkc::sequence::length(pairs));
}
protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P,enabled:bool@P)->(result:(F,F,F,F,F,index)@P){return work(xs,ys,enabled);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    if implicit:
        source = source.replace('zkc::vector::elements(xs)', 'xs').replace('zkc::vector::elements(ys)', 'ys')
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('values', {'xs': ['2', '3'], 'ys': ['7', '11'], 'enabled': True})['result'] == ['47', '23', '12', '5', '13', '4']
    assert entry.run('filter-skips-body', {'xs': ['2', '3'], 'ys': ['7', '11'], 'enabled': False})['result'] == ['47', '23', '12', '0', '13', '4']
    assert entry.run('empty', {'xs': [], 'ys': [], 'enabled': False})['result'] == ['0', '0', '1', '0', '0', '0']
    entry.run('strict-zip', {'xs': [], 'ys': ['1'], 'enabled': False}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
@pytest.mark.parametrize('indexed', [False, True])
def test_total_finite_libraries_and_matrix_views(toolchain, journal, directory, flags, indexed):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::matrix::{Matrix};
use zkc::finite_math as total;
domain F=field("koala-bear");
math fn analytic(xs:Vector<F>,matrix:Matrix<F>)->(F,F,F){
 let energy=total::sum(zkc::vector::indices(xs),fn(i)=>zkc::vector::at(xs,i)*zkc::vector::at(xs,i));
 let coordinates=total::sum(zkc::matrix::coordinates(matrix),fn((i,j))=>zkc::matrix::at(matrix,i,j));
 let nested=total::sum(zkc::matrix::row_indices(matrix),fn(i)=>total::sum(zkc::matrix::row_values(matrix,i),fn(x)=>x));
 return(energy,coordinates,nested);
}
protocol Run roles(P)(xs:Vector<F>@P,matrix:Matrix<F>@P)->(result:(F,F,F)@P){return analytic(xs,matrix);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    if indexed:
        source = source.replace('::{Vector}', '::{Vector,indexing []}').replace('::{Matrix}', '::{Matrix,indexing []}')
        source = source.replace('zkc::vector::at(xs,i)', 'xs[i]').replace('zkc::matrix::at(matrix,i,j)', 'matrix[i,j]')
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    matrix = {'rows': '2', 'columns': '3', 'entries': [['0', '0', '2'], ['1', '2', '7']]}
    assert entry.run('values', {'xs': ['2', '3'], 'matrix': matrix})['result'] == ['13', '9', '9']
    assert entry.run('empty', {'xs': [], 'matrix': {'rows': '0', 'columns': '3', 'entries': []}})['result'] == ['0', '0', '0']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_groups_records_filters_and_dependent_domains(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::curve::{Groups};
use zkc::finite as finite;
use zkc::finite_domain as domains;
domain G=group("bls12-381.g1");
struct Row{pub value:G::Scalar,pub enabled:bool}
fn checked_inverse(x:G::Scalar)->G::Scalar=primitive("field.inverse");
fn work(xs:Vector<G::Scalar>,n:index)->(bool,G::Scalar,G::Scalar,index){
 let generator=kernel<G>("curve.generator");
 let points=zkc::curve::collect(zkc::vector::elements(xs),fn(x)=>generator);
 let commitment=finite::group_sum(domains::zip(zkc::curve::elements(points),zkc::vector::elements(xs)),fn((point,x))=>point*x);
 let expected=generator*zkc::vector::sum(xs);
 let records=finite::collect(zkc::vector::elements(xs),fn(x)=>Row{value:x,enabled:!(x==0)});
 let selected=finite::sum_where(zkc::sequence::elements(records),fn(record)=>record.enabled,fn(record)=>record.value*checked_inverse(record.value));
 let ratio=finite::product_where(zkc::sequence::elements(records),fn(record)=>record.enabled,fn(record)=>record.value*checked_inverse(record.value));
 let triangular:index=finite::fold(domains::range(0,n),0,fn(state, i)=>state+finite::fold(domains::range(0,i),0,fn(count, j)=>count+1));
 return(commitment==expected,selected,ratio,triangular);
}
protocol Run roles(P)(xs:Vector<G::Scalar>@P,n:index@P)->(result:(bool,G::Scalar,G::Scalar,index)@P){return work(xs,n);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('values', {'xs': ['0', '2', '3'], 'n': 4})['result'] == [True, '2', '1', '6']
    assert entry.run('empty', {'xs': [], 'n': 0})['result'] == [True, '0', '1', '0']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_materialized_reducer_and_unfiltered_failure(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::vector::{Vector};
domain F=field("koala-bear");
fn invert(x:F)->F=primitive("field.inverse");
fn work(xs:Vector<F>,enabled:bool)->F{
 return zkc::vector::reduce(zkc::vector::elements(xs),fn(x)=>invert(x),fn(values)=>{
   require enabled;
   require zkc::vector::length(values)==2;
   zkc::vector::get(values,0)+zkc::vector::get(values,1)
 });
}
protocol Run roles(P)(xs:Vector<F>@P,enabled:bool@P)->(result:F@P){return work(xs,enabled);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('values', {'xs': ['1', '1'], 'enabled': True})['result'] == '2'
    entry.run('empty-still-calls-reducer', {'xs': [], 'enabled': True}, refuses='entry-host-run-failed')
    failure = entry.run('body-before-reducer', {'xs': ['0'], 'enabled': False}, refuses='entry-host-run-failed')
    assert 'refused:zero-inverse' in str(failure)
    failure = entry.run('reducer-failure', {'xs': ['1', '1'], 'enabled': False}, refuses='entry-host-run-failed')
    assert joint_execution(failure)['roles'][0]['after'][1]['cause'] == ['explicit', {'omitted_bytes': 0, 'text': 'reject'}]


def test_finite_library_project(toolchain, journal, directory):
    source = (ROOT / 'common/tests/fixtures/projects/finite-computations/main.zkc').read_text().replace('module example;', 'module sample;')
    entry = Entry(toolchain, journal, directory, source, MODULES)
    matrix = {'rows': '2', 'columns': '3', 'entries': [['0', '0', '2'], ['1', '2', '7']]}
    assert entry.run('example', {'xs': ['2', '3'], 'ys': ['7', '11'], 'matrix': matrix}) == {
        'dot': '47', 'square_sum': '13', 'selected_sum': '5', 'matrix_total': '9'}


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk'],
                                  ['--no-simplify', '--no-finite-bulk']])
@pytest.mark.parametrize('symbolic', [False, True])
def test_field_finite_calls_keep_bulk_execution(toolchain, journal, directory, flags, symbolic):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::finite as finite;
use zkc::finite_domain as domains;
domain F=field("koala-bear");
fn work(count:index,a:F,b:F,scale:F,shift:F)->(F,F,F){
 let xs=zkc::vector::fill(a,count);
 let ys=zkc::vector::fill(b,count);
 let dot=finite::sum(domains::zip(xs,ys),fn((x,y))=>x*y);
 let square=finite::sum(xs,fn(x)=>x*x);
 let mapped=zkc::vector::collect(xs,fn(x)=>x*scale+shift);
 let affine=zkc::vector::sum(mapped);
 return(dot,square,affine);
}
protocol Run roles(P)(count:index@P,a:F@P,b:F@P,scale:F@P,shift:F@P)->(result:(F,F,F)@P){return work(count,a,b,scale,shift);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    if symbolic:
        source = source.replace('finite::sum(domains::zip(xs,ys),fn((x,y))=>x*y)',
                                '∑ (x,y) in domains::zip(xs,ys),x*y')
        source = source.replace('finite::sum(xs,fn(x)=>x*x)', '∑ x in xs,x*x')
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    # Default preparation recognizes contractions at the container ceiling.
    # Finite selection is independent of generic simplification. Exercise
    # explicit loop fallback at a smaller size under the same capacity.
    fallback = '--no-finite-bulk' in flags
    count = 1024 if fallback else 2**16
    assert entry.run('large', {'count': str(count), 'a': '3', 'b': '7', 'scale': '2', 'shift': '5'})['result'] == [str(21*count), str(9*count), str(11*count)]
    report = json.loads(journal.last.stdout)
    iterations = joint_execution(report)['roles'][0]['usage']['iterations']
    assert iterations > 0 if fallback else iterations == 0


def test_named_group_sum_keeps_msm_execution(toolchain, journal, directory):
    source = '''module sample;
use zkc::curve::{Groups};
use zkc::finite as finite;
use zkc::finite_domain as domains;
domain G=group("bls12-381.g1");
fn work(value:G::Scalar)->bool{
 let base=kernel<G>("curve.generator");
 let mut points=kernel<G>("curve.append",kernel<G>("curve.empty"),base);
 for i in 0..12 {points=kernel<G>("curve.concat",points,points);}
 let scalars=zkc::vector::fill(value,4096);
 let commitment=finite::group_sum(domains::zip(points,scalars),fn((point,scalar))=>point*scalar);
 return commitment==base*(value*4096);
}
protocol Run roles(P)(value:G::Scalar@P)->(result:bool@P){return work(value);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, MODULES)
    assert entry.run('large', {'value': '3'})['result'] is True
    report = json.loads(journal.last.stdout)
    assert joint_execution(report)['roles'][0]['usage']['iterations'] == 12


def test_named_matrix_views_keep_contractions(toolchain, journal, directory):
    source = '''module sample;
use zkc::matrix::{Matrix};
use zkc::finite as finite;
use zkc::finite_domain as domains;
domain F=field("koala-bear");
fn work(matrix:Matrix<F>,value:F,selected:index)->(F,F){
 let xs=zkc::vector::fill(value,zkc::matrix::columns(matrix));
 let ys=zkc::vector::fill(value,zkc::matrix::rows(matrix));
 let row=finite::sum(domains::zip(zkc::matrix::row_values(matrix,selected),xs),fn((x,y))=>x*y);
 let column=finite::sum(domains::zip(zkc::matrix::column_values(matrix,0),ys),fn((x,y))=>x*y);
 return(row,column);
}
protocol Run roles(P)(matrix:Matrix<F>@P,value:F@P,selected:index@P)->(result:(F,F)@P){return work(matrix,value,selected);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, MODULES)
    matrix = {'rows': '2', 'columns': str(2**16), 'entries': [['0', '0', '2'], ['1', str(2**16-1), '7']]}
    assert entry.run('large', {'matrix': matrix, 'value': '3', 'selected': '1'})['result'] == ['21', '6']
    report = json.loads(journal.last.stdout)
    assert joint_execution(report)['roles'][0]['usage']['iterations'] == 0
    entry.run('out-of-bounds-view', {'matrix': matrix, 'value': '3', 'selected': '2'}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
@pytest.mark.parametrize('mode,module', [('fn', 'finite'), ('math fn', 'finite_math')])
def test_public_filtered_and_total_combinators(toolchain, journal, directory, flags, mode, module):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::accumulation::{Combiner};
use zkc::FINITE_MODULE as finite;
use zkc::finite_domain as domains;
domain F=field("koala-bear");
module Decimal:Combiner<F>{
 math fn identity()->F{return 0;}
 math fn combine(state:F,value:F)->F{return state*10+value;}
}
MODE compute(xs:Vector<F>,enabled:bool)->(F,F,F,F,F,F,F,F,F,F,F){
 let folded=finite::fold(xs,7,fn(state, x)=>state*10+x);
 let filtered=finite::fold_where(xs,7,fn(x)=>enabled,fn(state, x)=>state*10+x);
 let accumulated=finite::accumulate<F,F,Decimal>(xs,fn(x)=>x);
 let selected=finite::accumulate_where<F,F,Decimal>(xs,fn(x)=>enabled,fn(x)=>x);
 let values=finite::collect(xs,fn(x)=>x+1);
 let kept=finite::collect_where(xs,fn(x)=>enabled,fn(x)=>x+1);
 let values_sum=finite::sum(values,fn(x)=>x);
 let kept_sum=finite::sum(kept,fn(x)=>x);
 let product=finite::product(xs,fn(x)=>x);
 let product_kept=finite::product_where(xs,fn(x)=>enabled,fn(x)=>x);
 let sum_kept=finite::sum_where(xs,fn(x)=>enabled,fn(x)=>x);
 let array=[1,2];
 let array_sum=finite::sum(domains::array<F,2>(array),fn(x)=>x);
 let implicit_array_sum:F=finite::sum([1,2],fn(x)=>x);
 return(folded,filtered,accumulated,selected,values_sum,kept_sum,product,product_kept,sum_kept,array_sum,implicit_array_sum);
}
protocol Run roles(P)(xs:Vector<F>@P,enabled:bool@P)->(result:(F,F,F,F,F,F,F,F,F,F,F)@P){return compute(xs,enabled);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''.replace('FINITE_MODULE', module).replace('MODE', mode).replace('let array=[1,2];', 'let array:[F;2]=[1,2];')
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('values', {'xs': ['2', '3'], 'enabled': True})['result'] == ['723', '723', '23', '23', '7', '7', '6', '6', '5', '3', '3']
    assert entry.run('none-kept', {'xs': ['2', '3'], 'enabled': False})['result'] == ['723', '7', '23', '0', '7', '0', '6', '1', '0', '3', '3']
    assert entry.run('empty', {'xs': [], 'enabled': True})['result'] == ['7', '7', '0', '0', '0', '0', '1', '1', '0', '3', '3']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
@pytest.mark.parametrize('mode,module', [('fn', 'finite'), ('math fn', 'finite_math')])
def test_public_group_accumulation_modes_and_filters(toolchain, journal, directory, flags, mode, module):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::FINITE_MODULE as finite;
domain G=group("bls12-381.g1");
MODE compute(xs:Vector<G::Scalar>,point:G,enabled:bool)->(G,G,G::Scalar){
 let all=finite::group_sum(xs,fn(x)=>point*x);
 let kept=finite::group_sum_where(xs,fn(x)=>enabled,fn(x)=>point*x);
 return(all,kept,finite::sum(xs,fn(x)=>x));
}
fn work(xs:Vector<G::Scalar>,enabled:bool)->(bool,bool){
 let generator=kernel<G>("curve.generator");
 let (all,kept,total)=compute(xs,generator,enabled);
 let expected=generator*total;
 let selected=if enabled {expected} else {generator*0};
 return(all==expected,kept==selected);
}
protocol Run roles(P)(xs:Vector<G::Scalar>@P,enabled:bool@P)->(result:(bool,bool)@P){return work(xs,enabled);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''.replace('FINITE_MODULE', module).replace('MODE', mode)
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    for label, values, enabled in [('values', ['2', '3'], True), ('none-kept', ['2', '3'], False), ('empty', [], True)]:
        assert entry.run(label, {'xs': values, 'enabled': enabled})['result'] == [True, True]


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_symbolic_finite_calls_filters_precedence_and_nesting(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::finite::{reduction ∑,reduction ∏};
use zkc::finite_domain::{zip,range};
domain F=field("koala-bear");
fn inverted(x:F)->F=primitive("field.inverse");
protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P,enabled:bool@P,n:index@P)->(result:(F,F,F,F,F,F,F,F)@P){
 let dot@P=∑ (x,y) ∈ zip(xs,ys), x*y;
 let square@P=∑ x in xs, x*x;
 let shifted@P=∏ x ∈ xs, (x+1);
 let filtered@P=∑ x ∈ xs with enabled, inverted(x);
 let product@P=∑ (x ∈ xs) (y ∈ ys), x*y;
 let nested@P=∑ x ∈ xs, (∑ y ∈ ys, x*y);
 let triangular:F@P=∑ i ∈ range(0,n), (∑ j ∈ range(0,i), 1);
 let precedence@P=∑ x ∈ xs, x + 1;
 return(dot,square,shifted,filtered,product,nested,triangular,precedence);
}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('values', {'xs': ['1', '1'], 'ys': ['7', '11'], 'enabled': True, 'n': 4})['result'] == ['18', '2', '4', '2', '36', '36', '6', '3']
    assert entry.run('skip-failing-body', {'xs': ['0', '1'], 'ys': ['7', '11'], 'enabled': False, 'n': 0})['result'] == ['11', '1', '2', '0', '18', '18', '0', '2']
    assert entry.run('empty', {'xs': [], 'ys': [], 'enabled': True, 'n': 0})['result'] == ['0', '0', '1', '0', '0', '0', '0', '1']
    entry.run('strict-zip', {'xs': [], 'ys': ['1'], 'enabled': False, 'n': 0}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('explicit', [False, True])
def test_local_and_math_notation_require_an_explicit_choice(toolchain, journal, directory, explicit):
    source = directory / 'choice.zkc'
    source.write_text('''module sample;
use zkc::vector as vector;
use zkc::finite_math as total;
domain F=field("koala-bear");
math fn work(xs:vector::Vector<F>)->F {
 BINDING
 return ∑ x in xs with true,x*x;
}
'''.replace('BINDING', 'reduction ∑=total::sum,total::sum_where;' if explicit else ''))
    journal.run([toolchain.compiler, 'language-check', '--source-format=zkc',
                 f'--module=sample={source}', *MODULES],
                refuses=None if explicit else 'source.notation-ambiguous')


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_indexing_rebinding_and_direct_protocol(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::vector::{Vector,indexing []};
use zkc::finite_math as finite;
domain F=field("koala-bear");
fn selected(xs:Vector<F>,i:index)->F{
 indexing values[position]=zkc::vector::get(values,position);
 return xs[i];
}
protocol Run roles(P)(xs:Vector<F>@P,i:index@P)->(result:(F,F)@P){
 let total@P=finite::sum(zkc::vector::indices(xs),fn(j)=>xs[j]);
 let picked@P=selected(xs,i);
 return(total,picked);
}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('values', {'xs': ['2', '3'], 'i': '1'})['result'] == ['5', '3']
    entry.run('bounds', {'xs': [], 'i': '0'}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_indexing_across_collection_representations(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::field_array::{Array,indexing []};
use zkc::sequence::{Sequence,indexing []};
use zkc::curve::{Groups,indexing []};
use zkc::indices::{Indices,indexing []};
use zkc::finite as finite;
use zkc::finite_math as total;
domain G=group("bls12-381.g1");
struct Row{pub value:G::Scalar}
math fn combined(xs:Array<G::Scalar,2>,rows:Sequence<Row>,points:Groups<G>,values:Indices)->(G::Scalar,G::Scalar,G,bool){
 let array_sum=total::sum(zkc::field_array::indices(xs),fn(i)=>xs[i]);
 let record_sum=total::sum(zkc::sequence::indices(rows),fn(i)=>{let row=rows[i];row.value});
 let group_sum=total::group_sum(zkc::curve::indices(points),fn(i)=>points[i]);
 let same=total::fold(zkc::indices::indices(values),true,fn(state, i)=>state&&(values[i]==7));
 return(array_sum,record_sum,group_sum,same);
}
fn work(xs:Array<G::Scalar,2>)->(G::Scalar,G::Scalar,bool,bool){
 let generator=kernel<G>("curve.generator");
 let rows=finite::collect(xs,fn(value)=>Row{value:value});
 let points=zkc::curve::collect(xs,fn(value)=>generator);
 let values=zkc::indices::collect(xs,fn(value)=>7);
 let results=combined(xs,rows,points,values);
 return(results.0,results.1,results.2==generator+generator,results.3);
}
protocol Run roles(P)(xs:Array<G::Scalar,2>@P)->(result:(G::Scalar,G::Scalar,bool,bool)@P){return work(xs);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('values', {'xs': ['2', '3']})['result'] == ['5', '5', True, True]


def test_matrix_demand_example(toolchain, journal, directory):
    source = (ROOT / 'common/tests/fixtures/projects/finite-computations/main.zkc').read_text()
    source = source.replace('module example;', 'module sample;')
    entry = Entry(toolchain, journal, directory, source, MODULES, entry='MatrixDemo')
    matrix = {'rows': '2', 'columns': '3', 'entries': [['0', '0', '2'], ['1', '2', '7']]}
    assert entry.run('matrix-demands', {'matrix': matrix, 'xs': ['3', '5', '11'],
                                        'row': 1, 'seed': '13'}) == {
        'selected': '77', 'rows': ['19', '90']}
    entry.run('selected-row-bounds', {'matrix': matrix, 'xs': ['3', '5', '11'],
                                     'row': 2, 'seed': '13'}, refuses='entry-host-run-failed')
