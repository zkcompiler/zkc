"""General finite source functions through independent compilation and Host execution."""
import pytest

from entry import Entry

PREFIX = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
type Sequence<T:Type+Copy+Drop>=builtin("sequence",T);
domain fn elements<E:Field>(xs:Vector<E>)->domain<E>=domain("elements");
domain fn indices<E:Field>(xs:Vector<E>)->domain<index>=domain("indices");
domain fn sequence<T:Type+Copy+Drop>(xs:Sequence<T>)->domain<T>=domain("elements");
domain fn range(lower:index,upper:index)->domain<index>=domain("range");
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(left:domain<A>,right:domain<B>)->domain<(A,B)>=domain("zip");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn filtered<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,keep:fn(item:I)->bool effects(stop) where item_from(item, rows),step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold_where");
fn collect<I:Type+Copy+Drop,B:Type+Copy+Drop>(rows:domain<I>,body:fn(item:I)->B effects(stop) where item_from(item, rows))->Sequence<B> effects(stop)=finite("local.collect.sequence");
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
 let ordered=fold(elements(xs),initial,fn(state, item)=>state*10+item+offset);
 let mixed=fold(elements(xs),(initial,offset),fn((a,b), item)=>(b,item));
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
 return filtered(zip(elements(xs),elements(ys)),0,fn(item)=>enabled,
                 fn(state, item)=>{stop "abort";});
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
 let checked=fold(sequence(xs),(),fn(state, row)=>{require row.enabled;state});
 return collect(sequence(xs),fn(row)=>Row{value:row.value+1,enabled:row.enabled});
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
 let triangular=fold(indices(xs),0,fn(outer, i)=>outer+fold(range(0,i),0,fn(inner, j)=>inner+get(xs,j)));
 let mut shift=offset;
 let snapshots=fold(step=fn(state, item)=>state+item+shift,
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
 let first=fold(pairs,0,fn(state, (left,right))=>state+left.value*right.value);
 let second=fold(pairs,1,fn(state, (left,right))=>state+left.value+right.value);
 return(first,second);
}
protocol Run roles(P)(xs:Sequence<Row>@P)->(result:(F,F)@P){return work(xs);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('empty', {'xs': []})['result'] == ['0', '1']
    records = record_inputs(toolchain, journal, directory, flags)
    xs = records.run('input', {'a': '2', 'b': '3', 'enabled': True})['xs']
    assert entry.run('records', {'xs': xs})['result'] == ['13', '11']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_generic_item_restrictions_through_nested_scopes(toolchain, journal, directory, flags):
    source = PREFIX + '''
fn apply<A:Type,B:Type>(value:A,body:fn(A)->B effects(stop))->B effects(stop){return body(value);}
fn sum(rows:domain<F>,flag:bool,body:fn(item:F)->F effects(stop) where item_from(item, rows))->F effects(stop){
 return fold(step=fn(state, item)=>apply(state,fn(initial)=>{
   let mut total:F=initial;
   for i in 0..2 {let value=if flag {body(item)} else {0};total=total+value;}
   total
 }),rows=rows,initial=0);
}
protocol Run roles(P)(xs:Vector<F>@P,flag:bool@P,shift:F@P)->(result:F@P){
 return sum(elements(xs),flag,fn(item)=>item+shift);
}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('empty', {'xs': [], 'flag': True, 'shift': '4'})['result'] == '0'
    assert entry.run('selected', {'xs': ['2', '3'], 'flag': True, 'shift': '4'})['result'] == '26'
    assert entry.run('skipped', {'xs': ['2', '3'], 'flag': False, 'shift': '4'})['result'] == '0'


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_fixed_arrays_preserve_elements_indices_and_empty_unit(toolchain, journal, directory, flags):
    source = PREFIX + '''
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
domain fn array_indices<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<index>=domain("indices");
fn work(a:F,b:F)->(F,F,F,F){
 let xs=[a,b];
 let order=fold(array(xs),0,fn(state, item)=>state*10+item);
 let positions:F=fold(array_indices(xs),0,fn(state, item)=>state+1);
 let empty:[F;0]=[];
 let units=[(),(),()];
 let zero=fold(array(empty),a,fn(state, item)=>state+item);
 let three:F=fold(array(units),0,fn(state, item)=>state+1);
 return(order,positions,zero,three);
}
protocol Run roles(P)(a:F@P,b:F@P)->(result:(F,F,F,F)@P){return work(a,b);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('arrays', {'a': '2', 'b': '7'})['result'] == ['27', '2', '2', '3']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_fixed_record_arrays_zip_and_capture_original(toolchain, journal, directory, flags):
    source = PREFIX + '''
struct Row {pub value:F,pub enabled:bool}
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
fn work(a:F,b:F)->F{
 let xs=[Row{value:a,enabled:true},Row{value:b,enabled:true}];
 let ys=[b,a];
 return fold(zip(array(xs),array(ys)),0,fn(state, (row,other))=>{
   require row.enabled;
   state+row.value*other+xs[0].value
 });
}
protocol Run roles(P)(a:F@P,b:F@P)->(result:F@P){return work(a,b);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('records', {'a': '2', 'b': '7'})['result'] == '32'


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_total_fixed_array_fold_realization(toolchain, journal, directory, flags):
    source = PREFIX + '''
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold");
math fn work(a:F,b:F)->F{return total(array([(a,b),(b,a)]),0,fn(state, (x,y))=>state*100+x*10+y);}
protocol Run roles(P)(a:F@P,b:F@P)->(result:F@P){return work(a,b);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('total', {'a': '2', 'b': '7'})['result'] == '2772'


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_total_index_range_and_predicate(toolchain, journal, directory, flags):
    source = PREFIX + '''
math fn total_filtered<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,keep:math fn(item:I)->bool where item_from(item, rows),step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold_where");
math fn threshold<N:nat>()->index{return index<N>();}
math fn work(n:index)->(F,bool,index){
 let result:F=total_filtered(range(0,n),0,fn(i)=>intrinsic("index.less",i,threshold<2>()),fn(state, item)=>state+1);
 return(result,intrinsic("index.equal",n,2),18446744073709551615);
}
protocol Run roles(P)(n:index@P)->(result:(F,bool,index)@P){return work(n);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('empty', {'n': 0})['result'] == ['0', False, '18446744073709551615']
    assert entry.run('two', {'n': 2})['result'] == ['2', True, '18446744073709551615']
    assert entry.run('filtered', {'n': 5})['result'] == ['2', False, '18446744073709551615']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_total_bounds_on_distinct_captures_records_and_coordinates(toolchain, journal, directory, flags):
    source = PREFIX + '''
type Matrix<E:Field>=builtin("matrix",E);
struct Row {pub value:F,pub enabled:bool}
domain fn positions(xs:Sequence<Row>)->domain<index>=domain("indices");
domain fn coords(xs:Matrix<F>)->domain<(index,index)>=domain("matrix.coordinates.row_major");
domain fn row_indices(xs:Matrix<F>)->domain<index>=domain("indices.rows");
domain fn row(xs:Matrix<F>,i:index)->domain<F>=domain("matrix.row");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,step:math fn(S,item:I)->S where item_from(item, rows))->S=finite("math.fold");
math fn at(xs:Vector<F>,i:index)->F where in_bounds(i,xs){return intrinsic<Vector<F>>("container.at",xs,i);}
math fn read(xs:Sequence<Row>,i:index)->Row where in_bounds(i,xs){return intrinsic<Sequence<Row>>("container.at",xs,i);}
math fn inner(xs:Vector<F>,ys:Vector<F>)->F where equal_extent(xs,ys){return total(indices(xs),0,fn(s, i)=>s+at(ys,i));}
math fn work(xs:Vector<F>,rows:Sequence<Row>,matrix:Matrix<F>)->(F,F,F,F){
 let first=inner(xs,xs);
 let records:F=total(positions(rows),0,fn(s, i)=>{let record=read(rows,i);s+record.value});
 let entries:F=total(coords(matrix),0,fn(s, (i,j))=>s+intrinsic<Matrix<F>>("matrix.at",matrix,i,j));
 let nested:F=total(row_indices(matrix),0,fn(outer, i)=>outer+total(row(matrix,i),0,fn(row_state, item)=>row_state+item));
 return(first,records,entries,nested);
}
protocol Run roles(P)(xs:Vector<F>@P,rows:Sequence<Row>@P,matrix:Matrix<F>@P)->(result:(F,F,F,F)@P){return work(xs,rows,matrix);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    empty_matrix = {'rows': '0', 'columns': '3', 'entries': []}
    assert entry.run('empty', {'xs': [], 'rows': [], 'matrix': empty_matrix})['result'] == ['0', '0', '0', '0']
    records = record_inputs(toolchain, journal, directory, flags)
    rows = records.run('input', {'a': '3', 'b': '9', 'enabled': True})['xs']
    matrix = {'rows': '2', 'columns': '3', 'entries': [[0, 0, '2'], [1, 2, '7']]}
    assert entry.run('total', {'xs': ['5', '8'], 'rows': rows, 'matrix': matrix})['result'] == ['13', '12', '9', '9']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_total_fixed_zip_collection(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("bls12-381.fr");
type Array<E:Field,N:nat>=builtin("field_array",E,N);
domain fn array<T:Type+Copy+Drop,N:nat>(xs:[T;N])->domain<T>=domain("source_array");
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
math fn collect<I:Type+Copy+Drop,N:nat>(rows:domain<I>,body:math fn(item:I)->F where item_from(item, rows))->Array<F,N>=finite("math.collect.field_array");
math fn work(xs:[F;2],ys:[F;2])->Array<F,2>{return collect(zip(array(xs),array(ys)),fn((x,y))=>x+10*y);}
protocol Run roles(P)(xs:[F;2]@P,ys:[F;2]@P)->(result:Array<F,2>@P){return work(xs,ys);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('total', {'xs': ['2', '3'], 'ys': ['7', '11']})['result'] == ['72', '113']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_callback_origins_arbitrary_slots_and_independent_inputs(toolchain, journal, directory, flags):
    source = PREFIX + '''
fn item_first(rows:domain<F>,initial:F,
 step:fn(item:F,state:F)->F effects(stop) where item_from(item,rows))->F effects(stop){
 return fold(rows,initial,fn(state,item)=>step(item,state));
}
fn grid(rows:domain<F>,columns:domain<F>,
 term:fn(column:F,F,row:F)->F effects(stop)
 where item_from(row,rows),item_from(column,columns))->F effects(stop){
 return item_first(rows,0,fn(row,state)=>state+
   item_first(columns,0,fn(column,total)=>total+term(column,1,row)));
}
protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P)->(result:F@P){
 return grid(elements(xs),elements(ys),fn(c,offset,r)=>r*10+c+offset);
}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('grid', {'xs': ['2', '3'], 'ys': ['4', '5']})['result'] == '122'
    assert entry.run('empty', {'xs': [], 'ys': ['4']})['result'] == '0'
