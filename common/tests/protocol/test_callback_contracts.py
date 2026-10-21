"""Effect and input-origin contracts together through native execution."""

import pytest

from entry import Entry

PREFIX = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
domain fn elements<E:Field>(xs:Vector<E>)->domain<E>=domain("elements");
domain fn indices<E:Field>(xs:Vector<E>)->domain<index>=domain("indices");
fn fold<I:Type+Copy+Drop,S:Type>(
 rows:domain<I>,initial:S,
 step:fn(state:S,item:I)->S effects(stop) where item_from(item,rows)
)->S=finite("local.fold");
fn apply<A:Type,B:Type>(value:A,body:fn(A)->B)->B effects(body){return body(value);}
'''


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_effect_dependencies_through_module_and_nested_capture(
        toolchain, journal, directory, flags):
    source = PREFIX + '''
interface Transform {
 fn run(value:F,first:fn(F)->F,second:fn(F)->F)->F effects(first,second);
}
module Pipeline:Transform {
 fn run(value:F,first:fn(F)->F,second:fn(F)->F)->F {
  return apply(value,fn(x)=>apply(first(x),fn(y)=>second(y)));
 }
}
fn through<C:Transform>(x:F,first:fn(F)->F,second:fn(F)->F)->F effects(first,second){
 return C::run(x,first,second);
}
fn work(x:F)->F effects(){return through<Pipeline>(x,fn(y)=>y+1,fn(y)=>y*2);}
protocol Run roles(P)(x:F@P)->(result:F@P){return work(x);}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('composed', {'x': '3'})['result'] == '8'


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_two_domain_origins_through_nested_callbacks(
        toolchain, journal, directory, flags):
    source = PREFIX + '''
fn grid(rows:domain<F>,columns:domain<F>,
 term:fn(row:F,column:F)->F effects(stop)
  where item_from(row,rows),item_from(column,columns)
)->F {
 return fold(rows,0,fn(outer,row)=>outer+
  fold(columns,0,fn(inner,column)=>inner+term(row,column)));
}
protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P)->(result:F@P){
 return grid(elements(xs),elements(ys),fn(x,y)=>apply(x,fn(z)=>z*y));
}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('grid', {'xs': ['2', '3'], 'ys': ['5', '7']})['result'] == '60'
    assert entry.run('empty', {'xs': [], 'ys': ['5', '7']})['result'] == '0'


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_item_first_adapter_with_same_typed_state(
        toolchain, journal, directory, flags):
    source = PREFIX + '''
fn fold_item_first(rows:domain<F>,initial:F,
 step:fn(item:F,state:F)->F effects(stop) where item_from(item,rows)
)->F {return fold(rows,initial,fn(state,item)=>step(item,state));}
protocol Run roles(P)(xs:Vector<F>@P)->(result:F@P){
 return fold_item_first(elements(xs),0,fn(item,state)=>state*10+item);
}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('ordered', {'xs': ['2', '3', '5']})['result'] == '235'


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_math_grid_preserves_bounds_for_each_container(
        toolchain, journal, directory, flags):
    source = PREFIX + '''
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(
 rows:domain<I>,initial:S,
 step:math fn(state:S,item:I)->S where item_from(item,rows)
)->S=finite("math.fold");
math fn at(xs:Vector<F>,i:index)->F where in_bounds(i,xs){
 return intrinsic<Vector<F>>("container.at",xs,i);
}
math fn grid(rows:domain<index>,columns:domain<index>,
 term:math fn(row:index,column:index)->F
  where item_from(row,rows),item_from(column,columns)
)->F {
 return total(rows,0,fn(outer,row)=>outer+
  total(columns,0,fn(inner,column)=>inner+term(row,column)));
}
math fn work(xs:Vector<F>,ys:Vector<F>)->F{
 return grid(indices(xs),indices(ys),fn(i,j)=>at(xs,i)*at(ys,j));
}
protocol Run roles(P)(xs:Vector<F>@P,ys:Vector<F>@P)->(result:F@P){
 return work(xs,ys);
}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('bounds', {'xs': ['2', '3'], 'ys': ['5', '7']})['result'] == '60'
