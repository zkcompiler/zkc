"""Observe named binding and Boolean evaluation through the compiler and Host."""

import itertools

import pytest

from entry import Entry


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_named_calls_preserve_written_order_and_declared_types(
    toolchain, journal, directory, flags,
):
    source = '''module sample;
interface Ops<T:Type>{fn select(first:T,second:index)->(T,index);}
component Impl<T:Type>:Ops<T>{fn select(a:T,b:index)->(T,index){return(a,b);}}
fn abstract_call<C:Ops<bool>>(x:bool,n:index){return C::select(second=n,first=x);}
fn pair<A:Type,B:Type>(left:A,right:B){return(left,right);}
fn work(go:bool){
  let mut count:index=0;
  let values=pair<B=index>(right={count=count+1;count},left={count=count+1;go});
  let direct=Impl::select<T=bool>(b=count,a=go);
  let abstract=abstract_call<C=Impl<T=bool>>(n=count,x=go);
  return(values.0,values.1,count,direct.0,direct.1,abstract.0,abstract.1);
}
protocol Run roles(P)(go:bool@P)->(result:(bool,index,index,bool,index,bool,index)@P){
  return work(go=go);
}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for go in (False, True):
        assert entry.run(str(go), {'go': go}) == {
            'result': [go, 1, 2, go, 2, go, 2],
        }


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('protocol_call', [False, True])
def test_named_arguments_preserve_first_failure(
    toolchain, journal, directory, flags, protocol_call,
):
    callee = ('protocol Pair roles(P)(left:index@P,right:index@P)->(r:index@P)'
              if protocol_call else 'fn Pair(left:index,right:index)->index')
    source = f'''module sample;
fn reject(go:bool)->index{{if go{{stop "reject";}}return 1;}}
fn abort(go:bool)->index{{if go{{stop "abort";}}return 2;}}
fn add(a:index,b:index){{return a+b;}}
{callee}{{return add(left,right);}}
protocol Run roles(P)(first:bool@P,second:bool@P)->(r:index@P){{
  let r=Pair(right=abort(first),left=reject(second));return r;
}}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('success', {'first': False, 'second': False}) == {'r': 3}
    for first, reason in [(True, 'abort'), (False, 'reject')]:
        report = entry.run(reason, {'first': first, 'second': True},
                           refuses='entry-run-incomplete')
        assert report['execution']['roles'][0]['before'][1]['cause'] == [
            'explicit', {'omitted_bytes': 0, 'text': reason},
        ]


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_named_protocol_arguments_bind_the_selected_service(
    toolchain, journal, directory, flags,
):
    source = '''module sample;
domain F=field("bls12-381.fr");
protocol Draw roles(P)(first:Random<F>@P,go:bool@P,second:Random<F>@P)->(r:bool@P){
  let a=first.draw();require go;let b=second.draw();return a==b;
}
protocol Run roles(P)(go:bool@P,a:Random<F>@P,b:Random<F>@P)->(r:bool@P){
  let r=Draw(second=a,go=go,first=b);return r;
}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    # The first draw must use b's budget, then reject before reading exhausted a.
    report = entry.run_roles('reject', {
        'P': {'inputs': {'go': False}, 'services': {'a': 0, 'b': 1}},
    }, refuses='entry-run-incomplete')
    assert report['execution']['roles'][0]['before'][1]['cause'] == [
        'explicit', {'omitted_bytes': 0, 'text': 'reject'},
    ]


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_boolean_precedence_and_short_circuit_state(toolchain, journal, directory, flags):
    source = '''module sample;
math fn formula(a:bool,b:bool,c:bool){return !a || b && c==false;}
fn local(a:bool,b:bool,c:bool){return !a || b && c==false;}
fn observe(a:bool,b:bool){
  let mut count:index=0;
  let x=a && {count=count+1;b};
  let y=a || {count=count+2;b};
  return(x,y,count);
}
protocol Run roles(P)(a:bool@P,b:bool@P,c:bool@P)
  ->(formula_result:bool@P,local:bool@P,common:bool@P,state:(bool,bool,index)@P){
  return(formula_result=formula(c=c,a=a,b=b),local=local(c=c,b=b,a=a),
         common=!a || b && c==false,state=observe(b=b,a=a));
}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for a, b, c in itertools.product((False, True), repeat=3):
        expected = not a or b and not c
        assert entry.run(f'{a}-{b}-{c}', {'a': a, 'b': b, 'c': c}) == {
            'formula_result': expected, 'local': expected, 'common': expected,
            'state': [a and b, a or b, 1 if a else 2],
        }


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('operator,skip', [('&&', False), ('||', True)])
def test_short_circuit_skips_failures_but_keeps_eager_calls(
    toolchain, journal, directory, flags, operator, skip,
):
    source = f'''module sample;
math fn both(a:bool,b:bool){{return a&&b;}}
fn checked(b:bool){{require b;return b;}}
fn conditional(go:bool,ok:bool){{return go {operator} checked(ok);}}
fn eager(go:bool,ok:bool){{return both(go,checked(ok));}}
protocol Run roles(P)(go:bool@P,ok:bool@P,use_eager:bool@P)->(r:bool@P){{
  let r=choose(go,ok,use_eager);return r;
}}
fn choose(go:bool,ok:bool,use_eager:bool){{
  return if use_eager{{eager(go,ok)}}else{{conditional(go,ok)}};
}}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('skipped', {'go': skip, 'ok': False, 'use_eager': False}) == {'r': skip}
    for name, go, eager in [('reached', not skip, False), ('eager', skip, True)]:
        report = entry.run(name, {'go': go, 'ok': False, 'use_eager': eager},
                           refuses='entry-run-incomplete')
        assert report['execution']['roles'][0]['before'][1]['cause'] == [
            'explicit', {'omitted_bytes': 0, 'text': 'reject'},
        ]
