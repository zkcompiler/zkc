"""General finite source functions through independent compilation and Host execution."""
import pytest

from entry import Entry

PREFIX = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
domain fn elements<E:Field>(xs:Vector<E>)->scoped domain<E>=domain("elements");
domain fn indices<E:Field>(xs:Vector<E>)->scoped domain<index>=domain("indices");
domain fn sequence<T:Type+Copy+Drop>(xs:Sequence<T>)->scoped domain<T>=domain("elements");
domain fn range(lower:index,upper:index)->scoped domain<index>=domain("range");
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(left:scoped domain<A>,right:scoped domain<B>)->scoped domain<(A,B)>=domain("zip");
fn fold<I:Type+Copy+Drop,S:Type>(rows:scoped domain<I>,initial:S,step:scoped fn(S,I)->S !{stop} on(rows))->S !{stop}=finite("local.fold");
fn filtered<I:Type+Copy+Drop,S:Type>(rows:scoped domain<I>,initial:S,keep:scoped fn(I)->bool !{stop} on(rows),step:scoped fn(S,I)->S !{stop} on(rows))->S !{stop}=finite("local.fold_where");
fn collect<I:Type+Copy+Drop,B:Type+Copy+Drop>(rows:scoped domain<I>,body:scoped fn(I)->B !{stop} on(rows))->Sequence<B> !{stop}=finite("local.collect.sequence");
fn get<E:Field>(xs:Vector<E>,i:index)->E=primitive("vector.get");
'''


def record_inputs(toolchain, journal, directory, flags):
    # Sequences use the native wire codec for nominal products. Create the
    # fixture through source packing, then replay its authenticated output.
    source = PREFIX + '''
struct Row {pub value:F,pub enabled:bool}
fn empty<T:Type+Copy+Drop>()->Sequence<T>=primitive("sequence.empty");
fn append<T:Type+Copy+Drop>(xs:Sequence<T>,item:T)->Sequence<T>=primitive("sequence.append");
fn make(a:F,b:F,enabled:bool)->Sequence<Row>{
 return append(append(empty<Row>(),Row{value:a,enabled:enabled}),Row{value:b,enabled:enabled});
}
protocol Run roles(P)(a:F@P,b:F@P,enabled:bool@P)->(xs:Sequence<Row>@P){return make(a,b,enabled);}run Demo=Run;
'''
    path = directory / 'records'
    path.mkdir()
    return Entry(toolchain, journal, path, source, flags)


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_ordered_fold_initial_state_and_mixed_state(toolchain, journal, directory, flags):
    source = PREFIX + '''
fn work(xs:Vector<F>,initial:F,offset:F)->(F,(F,F)){
 let ordered=fold(elements(xs),initial,fun state item=>state*10+item+offset);
 let mixed=fold(elements(xs),(initial,offset),fun (a,b) item=>(b,item));
 return(ordered,mixed);
}
protocol Run roles(P)(xs:Vector<F>@P,initial:F@P,offset:F@P)->(result:(F,(F,F))@P){return work(xs,initial,offset);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('empty', {'xs': [], 'initial': '1', 'offset': '4'})['result'] == ['1', ['1', '4']]
    assert entry.run('ordered', {'xs': ['2', '3'], 'initial': '1', 'offset': '4'})['result'] == ['167', ['2', '3']]


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_filtered_body_skips_stops_and_still_admits_zip(toolchain, journal, directory, flags):
    source = PREFIX + '''
protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P,enabled:bool@P)->(result:F@P){
 return filtered(zip(elements(xs),elements(ys)),0,fun item=>enabled,
                 fun state item=>{stop "abort";});
}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('skipped', {'xs': ['2'], 'ys': ['3'], 'enabled': False})['result'] == '0'
    refused = entry.run('entered', {'xs': ['2'], 'ys': ['3'], 'enabled': True}, refuses='entry-run-incomplete')
    assert refused['execution']['roles'][0]['after'][1]['cause'] == ['explicit', {'omitted_bytes': 0, 'text': 'abort'}]
    entry.run('mismatch', {'xs': [], 'ys': ['3'], 'enabled': False}, refuses='entry-run-incomplete')


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_sequence_records_collect_and_unit_state(toolchain, journal, directory, flags):
    source = PREFIX + '''
struct Row {pub value:F,pub enabled:bool}
fn work(xs:Sequence<Row>)->Sequence<Row>{
 let checked=fold(sequence(xs),(),fun state row=>{require row.enabled;state});
 return collect(sequence(xs),fun row=>Row{value:row.value+1,enabled:row.enabled});
}
protocol Run roles(P)(xs:Sequence<Row>@P)->(result:Sequence<Row>@P){return work(xs);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('empty', {'xs': []})['result'] == []
    records = record_inputs(toolchain, journal, directory, flags)
    xs = records.run('input', {'a': '3', 'b': '9', 'enabled': True})['xs']
    expected = records.run('expected', {'a': '4', 'b': '10', 'enabled': True})['xs']
    assert entry.run('records', {'xs': xs})['result'] == expected
    rejected = records.run('rejected', {'a': '3', 'b': '9', 'enabled': False})['xs']
    entry.run('failed', {'xs': rejected}, refuses='entry-run-incomplete')


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_dependent_inner_domain_and_snapshot_order(toolchain, journal, directory, flags):
    source = PREFIX + '''
fn work(xs:Vector<F>,offset:F)->(F,F){
 let triangular=fold(indices(xs),0,fun outer i=>outer+fold(range(0,i),0,fun inner j=>inner+get(xs,j)));
 let mut shift=offset;
 let snapshots=fold(step=fun state item=>state+item+shift,
                    rows=elements({shift=shift+1;xs}),initial=0);
 return(triangular,snapshots);
}
protocol Run roles(P)(xs:Vector<F>@P,offset:F@P)->(result:(F,F)@P){return work(xs,offset);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('empty', {'xs': [], 'offset': '4'})['result'] == ['0', '0']
    assert entry.run('nested', {'xs': ['2', '3', '5'], 'offset': '4'})['result'] == ['7', '22']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_repeated_zipped_record_computations(toolchain, journal, directory, flags):
    source = PREFIX + '''
struct Row {pub value:F,pub enabled:bool}
fn work(xs:Sequence<Row>)->(F,F){
 let pairs=zip(sequence(xs),sequence(xs));
 let first=fold(pairs,0,fun state (left,right)=>state+left.value*right.value);
 let second=fold(pairs,1,fun state (left,right)=>state+left.value+right.value);
 return(first,second);
}
protocol Run roles(P)(xs:Sequence<Row>@P)->(result:(F,F)@P){return work(xs);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('empty', {'xs': []})['result'] == ['0', '1']
    records = record_inputs(toolchain, journal, directory, flags)
    xs = records.run('input', {'a': '2', 'b': '3', 'enabled': True})['xs']
    assert entry.run('records', {'xs': xs})['result'] == ['13', '11']
