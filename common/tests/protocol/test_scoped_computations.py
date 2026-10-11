"""Static scoped computations through compiler admission and native Host execution."""
import json
from pathlib import Path

import pytest

from entry import Entry
from input_files import decimal_values, input_files

ROOT = Path(__file__).resolve().parents[3]
LIBRARY = (ROOT / 'libraries/zkc/computation.zkc').read_text().replace(
    'module zkc::computation;', '')
PREFIX = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
fn get<E:Field>(xs:Vector<E>,i:index)->E=primitive("vector.get");
''' + LIBRARY


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_component_nested_callbacks_and_checked_lookup(toolchain, journal, directory, flags):
    package = directory / 'scoped.zkpkg'
    compiled = journal.json([
        toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--project={ROOT / "examples/projects/scoped-computations/zkc.toml"}',
        'example::Demo', f'--output={package}', *flags,
    ])
    for position, expected in [(0, 16), (1, None)]:
        request = input_files(journal, f'position-{position}.json', session='scoped', roles={
            'P': {'inputs': {'shared': '3', 'parameters': {'shift': '7', 'table': ['5']},
                             'position': str(position)}},
            'V': {'inputs': {'shared': '3'}},
        })
        output = directory / f'position-{position}.outputs.json'
        result = journal.json([
            toolchain.runtime, '--json', 'run', f'--package={package}',
            f'--sha256={compiled["package_sha256"]}', *request, f'--results={output}',
        ], refuses='entry-run-incomplete' if expected is None else None)
        if expected is None:
            assert result['execution']['roles'][0]['after'][1]['cause'] == [
                'backend', {'omitted_bytes': 0, 'text': 'refused:vector-index'}]
            assert not output.exists()
        else:
            assert json.loads(output.read_text())['roles']['P']['result'] == str(expected)


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_math_local_repeated_invocation_and_whole_record(toolchain, journal, directory, flags):
    source = PREFIX + '''
struct Params {pub a:F,pub b:F}
fn whole(p:Params,x:F)->F{return x+p.a-p.b;}
fn work(x:F,p:Params)->(F,F,F,F){
 let a=forward_math(x,fn(y)=>y+p.a-p.b);
 let b=forward(x,fn(y)=>whole(p,y));
 let c=twice(x,fn(y)=>whole(p,y));
 let d=forward(x,fn(y)=>{let mut state=y;for i in 0..2 {state=whole(p,state);}state});
 return(a,b,c,d);
}
protocol Run roles(P)(x:F@P,p:Params@P)->(result:(F,F,F,F)@P){return work(x,p);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('values', {'x': '3', 'p': {'a': '7', 'b': '2'}})['result'] == [
        '8', '8', '13', '13']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_named_argument_order_snapshots_and_distinct_bodies(toolchain, journal, directory, flags):
    source = PREFIX + '''
fn work(x:F)->(F,F,F,F){
 let mut a=x;
 let mut b=x+1;
 let first=apply(body=fn(y)=>y+a-b,value={a=a+1;b=b+1;x});
 let second=apply(value={a=a+1;b=b+1;x},body=fn(y)=>y+a+b);
 let third=apply(x,fn(y)=>y*a);
 let fourth=apply(x,fn(y)=>y*b);
 return(first,second,third,fourth);
}
protocol Run roles(P)(x:F@P)->(result:(F,F,F,F)@P){return work(x);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('snapshots', {'x': '3'})['result'] == ['2', '14', '15', '18']


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_protocol_callback_short_circuit_and_stops(toolchain, journal, directory, flags):
    source = PREFIX + '''
fn fail(x:bool)->bool !{stop}{require x;return x;}
protocol Run roles(P)(x:bool@P)->(result:bool@P){
 return apply(x,fn(y)=>y && fail(false));
}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('skipped', {'x': False})['result'] is False
    refused = entry.run('entered', {'x': True}, refuses='entry-run-incomplete')
    assert refused['execution']['roles'][0]['after'][1]['cause'] == [
        'explicit', {'omitted_bytes': 0, 'text': 'reject'}]


def test_multiple_inputs_tuple_patterns_and_environment_reuse(toolchain, journal, directory):
    source = PREFIX + '''
fn two(x:F,y:F,body:fn(F,F)->F !{})->F !{}{return body(x,y);}
fn pair(x:(F,F),body:fn((F,F))->F !{})->F !{}{return body(x);}
fn zero(body:fn()->F !{})->F !{}{return body();}
fn unit(body:fn(())->F !{})->F !{}{return body(());}
fn shift(x:F,a:F)->F{return forward(x,fn(y)=>y+a);}
fn work(x:F,a:F,b:F)->(F,F,F,F,F,F){return(two(x,a,fn(y,z,)=>y+z),pair((x,a),fn((y,z))=>y-z),shift(x,a),shift(x,b),zero(fn()=>x+a),unit(fn(())=>x+b));}
protocol Run roles(P)(x:F@P,a:F@P,b:F@P)->(result:(F,F,F,F,F,F)@P){return work(x,a,b);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source)
    assert entry.run('tuple-and-code-reuse', {'x': '9', 'a': '7', 'b': '2'})['result'] == decimal_values([16, 2, 16, 11, 16, 11])


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_matrix_array_captures_and_forwarded_callbacks_in_control(toolchain, journal, directory, flags):
    source = PREFIX + '''
type Matrix<E:Field>=builtin("matrix",E);
fn rows<E:Field>(m:Matrix<E>)->index{return kernel<E>("matrix.dimension",m;"0");}
fn select(x:F,go:bool,first:fn(F)->F !{stop},second:fn(F)->F !{stop})->F !{stop}{
 return if go{second(first(x))}else{first(second(x))};
}
fn relay(x:F,go:bool,first:fn(F)->F !{stop},second:fn(F)->F !{stop})->F !{stop}{
 return select(second=second,x=x,first=first,go=go);
}
fn work(x:F,a:[F;2],m:Matrix<F>,go:bool)->(F,index,F){
 let selected=relay(x,go,fn(y)=>y+a[0],fn(y)=>y*a[1]);
 let count=apply(0,fn(i)=>i+rows(m));
 let total=apply_math(x,fn(y)=>y+a[0]-a[1]);
 return(selected,count,total);
}
protocol Run roles(P)(x:F@P,a:[F;2]@P,m:Matrix<F>@P,go:bool@P)->(result:(F,index,F)@P){return work(x,a,m,go);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    inputs = {'x': '3', 'a': ['7', '2'],
              'm': {'rows': '2', 'columns': '2', 'entries': []}}
    assert entry.run('then', {**inputs, 'go': True})['result'] == ['20', '2', '8']
    assert entry.run('else', {**inputs, 'go': False})['result'] == ['13', '2', '8']


@pytest.mark.parametrize('count', [0, 3])
def test_affine_explicit_state_in_callback(toolchain, journal, directory, count):
    source = PREFIX + '''
struct Token:Drop {}
fn work(n:index)->bool{
 let token=apply(Token{},fn(x)=>{let mut state=x;for _ in 0..n {let old=state;consume old;state=Token{};}state});
 consume token;return true;
}
protocol Run roles(P)(n:index@P)->(result:bool@P){return work(n);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source)
    assert entry.run('state', {'n': str(count)})['result'] is True


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_domain_forwarding_and_callback_invariants_in_loops(toolchain, journal, directory, flags):
    source = PREFIX + '''

domain fn elements<E:Field>(xs:Vector<E>)->domain<E>=domain("elements");
fn ignore(rows:domain<F>,fallback:F)->F{return fallback;}
fn iterate(x:F,n:index,rows:domain<F>,body:fn(F)->F !{stop})->F !{stop}{
 let mut state=x;for _ in 0..n {state=ignore(rows,body(state));}return state;
}
fn outer(xs:Vector<F>,x:F,n:index)->F !{stop}{
 let rows=elements(xs);return iterate(x,n,rows,fn(y)=>ignore(rows,y+x));
}
protocol Run roles(P)(xs:Vector<F>@P,x:F@P,n:index@P)->(result:F@P){return outer(xs,x,n);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for count in (0, 3):
        assert entry.run(f'iterations-{count}', {'xs': ['4', '9'], 'x': '7', 'n': str(count)})['result'] == str(7 * (count + 1))


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_domains_and_callbacks_inside_protocol_repetition(toolchain, journal, directory, flags):
    source = PREFIX + '''
domain fn elements<E:Field>(xs:Vector<E>)->domain<E>=domain("elements");
fn ignore(rows:domain<F>,fallback:F)->F{return fallback;}
protocol Run roles(P,V)(xs:Vector<F>@P,x:F@P,n:index@(P,V))->(result:F@P){
 let rows=elements(xs);let mut result@P=x;
 for _ in 0..n roles(P,V) max 4 {
   for _ in 0..n roles(P,V) max 4 {result=apply(result,fn(y)=>ignore(rows,y+x));}
 }
 return result;
}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for count in (0, 2):
        outputs = entry.run_roles(f'iterations-{count}', {
            'P': {'inputs': {'xs': ['4', '9'], 'x': '7', 'n': str(count)}},
            'V': {'inputs': {'n': str(count)}},
        })
        assert outputs['P']['result'] == str(7 * (count * count + 1))
        assert outputs['V'] == {}


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_domain_captures_in_match_arms_with_different_payloads(toolchain, journal, directory, flags):
    source = PREFIX + '''
domain fn elements<E:Field>(xs:Vector<E>)->domain<E>=domain("elements");
enum Choice { Single(F), Pair(F,F) }
fn ignore(rows:domain<F>,fallback:F)->F{return fallback;}
fn choose(value:Choice,rows:domain<F>,body:fn(F)->F !{})->F !{}{
 return match value {
  Single(a)=>{body(ignore(rows,a))},
  Pair(a,b)=>{body(ignore(rows,a+b))}
 };
}
fn outer(xs:Vector<F>,x:F,paired:bool)->F{
 let rows=elements(xs);
 let value=if paired{Choice::Pair(x,x)}else{Choice::Single(x)};
 return choose(value,rows,fn(y)=>y+x);
}
protocol Run roles(P)(xs:Vector<F>@P,x:F@P,paired:bool@P)->(result:F@P){return outer(xs,x,paired);}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for paired, expected in [(False, '14'), (True, '21')]:
        assert entry.run(f'paired-{paired}', {
            'xs': ['4', '9'], 'x': '7', 'paired': paired,
        })['result'] == expected
