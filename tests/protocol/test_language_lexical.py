"""Check source elaboration against direct calculations through the common Host.

The MLIR emitter and source comparator share the elaborated graph. These expected
results therefore exercise a separate boundary from their structural agreement.
"""

import pytest

from entry import Entry


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_inferred_calls_use_independent_participant_components(
    toolchain, journal, directory, flags,
):
    source = '''module sample;
fn echo(x:index)->index{return x;}
fn add(x:index,y:index)->index{return kernel("index.add",x,y);}
protocol Run roles(P,V)(shared:index@(P,V),p:index@P)->(r:index@P,s:index@V){
  let r=add(echo(shared),p);
  return(r,s=echo(shared));
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run_roles('different-components', {
        'P': {'inputs': {'shared': 2, 'p': 3}}, 'V': {'inputs': {'shared': 9}},
    }) == {'P': {'r': 5}, 'V': {'s': 9}}


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_protocol_loop_tail_call_keeps_its_owner(toolchain, journal, directory, flags):
    source = '''module sample;
fn note(go:bool)->(){require go;return ();}
protocol Run roles(P,V)(n:index@(P,V),go:bool@P)->(result:bool@V){
  for _ in 0..n roles(P,V) max 4{note(go)}
  return true;
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for name, n, go in [('empty', 0, False), ('pass', 2, True)]:
        assert entry.run_roles(name, {
            'P': {'inputs': {'n': n, 'go': go}}, 'V': {'inputs': {'n': n}},
        }) == {'P': {}, 'V': {'result': True}}
    report = entry.run_roles('reject', {
        'P': {'inputs': {'n': 1, 'go': False}}, 'V': {'inputs': {'n': 1}},
    }, refuses='entry-run-incomplete')
    assert 'reject' in str(report)


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_scopes_state_joins_and_bounds_evaluated_once(toolchain, journal, directory, flags):
    source = '''module sample;
struct Counts { pub total:index, pub bound:index }
fn zero()->index { return 0; }
fn increment(x:index)->index { return kernel("index.add",x,1); }
fn work(n:index,m:index,go:bool)->Counts {
  let mut bound=n;
  let mut total:index=0;
  for i in 0..bound {
    bound=0;
    {
      let delta:index=if go { i } else { 1 };
      total=kernel("index.add",total,delta);
    }
    for _ in 0..m { total=increment(total); }
  }
  let total={let offset:index=2;kernel("index.add",total,offset)};
  return Counts{total,bound};
}
protocol Run roles(P)(n:index@P,m:index@P,go:bool@P)
  ->(local_total:index@P,local_bound:index@P,total:index@P,bound:index@P) {
  let Counts{total:local_total,bound:local_bound}@P=work(n,m,go);
  let mut total=local_total;
  let mut bound=n;
  for _ in 0..bound roles(P) max 8 {
    bound=zero();
    total=increment(total);
  }
  return(bound,total,local_bound,local_total);
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for n in (0, 1, 4, 8):
        for m in (0, 3):
            for go in (False, True):
                expected = (n * (n - 1) // 2 if go else n) + n * m + 2
                assert entry.run(f'{n}-{m}-{go}', {'n': n, 'm': m, 'go': go}) == {
                    'local_total': expected, 'local_bound': 0,
                    'total': expected + n, 'bound': 0,
                }
    entry.run('over-bound', {'n': 9, 'm': 0, 'go': False}, refuses='entry-run-incomplete')


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_all_stopped_regions_preserve_selected_stop(toolchain, journal, directory, flags):
    source = '''module sample;
struct Ticket:Share {}
fn work(go:bool)->index {
  let ticket=Ticket{};
  return if go { stop "reject"; } else { {stop "abort";} };
}
protocol Run roles(P)(go:bool@P)->(result:index@P) {
  let result@P=work(go);
  return result;
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for go in (False, True):
        report = entry.run(str(go), {'go': go}, refuses='entry-run-incomplete')
        assert ('reject' if go else 'abort') in str(report)


def test_stopping_loop_retains_zero_trip_state(toolchain, journal, directory):
    source = '''module sample;
struct Ticket:Share {}
fn work(n:index,go:bool)->index {
  let mut ticket=Ticket{};
  for _ in 0..n {
    ticket=ticket;
    if go {stop "reject";} else {stop "abort";}
  }
  consume ticket;
  return n;
}
protocol Run roles(P)(n:index@P,go:bool@P)->(result:index@P) {
  let result@P=work(n,go);return result;
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source)
    for go in (False, True):
        assert entry.run(f'empty-{go}', {'n': 0, 'go': go}) == {'result': 0}
        report = entry.run(f'stop-{go}', {'n': 2, 'go': go}, refuses='entry-run-incomplete')
        assert ('reject' if go else 'abort') in str(report)


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_restoration_and_nested_stopped_inference(toolchain, journal, directory, flags):
    source = '''module sample;
struct State:Drop { value:index }
struct Required:Copy {}
fn make(x:index)->State{return State{value:x};}
fn take(s:State)->index{let State{value}=s;return value;}
fn pair(a:index,s:State)->index{return kernel("index.add",a,take(s));}
fn work(x:index,go:bool,halt:bool)->index {
  let mut state=make(x);
  if go{consume state;}else{consume state;}
  let total=pair({state=make(x);x},state);
  let k=Required{};
  if go{consume k;}
  consume k;
  let result=if halt{
    if go{stop "reject";}else{stop "abort";}
  }else{total};
  return result;
}
protocol Run roles(P)(x:index@P,go:bool@P,halt:bool@P)->(result:index@P){
  let result@P=work(x,go,halt);return result;
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for go in (False, True):
        for halt in (False, True):
            inputs = {'x': 7, 'go': go, 'halt': halt}
            if halt:
                report = entry.run(f'{go}-{halt}', inputs, refuses='entry-run-incomplete')
                assert ('reject' if go else 'abort') in str(report)
            else:
                assert entry.run(f'{go}-{halt}', inputs) == {'result': 14}


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_require_outcomes_and_ordered_nested_calls(toolchain, journal, directory, flags):
    source = '''module sample;
fn checked(x:index,go:bool)->index {require go;return x;}
fn raw(x:index,go:bool)->index {let ()=kernel("control.require",go);return x;}
fn plus(a:index,b:index)->index {return kernel("index.add",a,b);}
protocol Run roles(P)(x:index@P,first:bool@P,second:bool@P)->(r:index@P){
  return plus(checked(x,first),raw(x,second));
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('pass', {'x': 7, 'first': True, 'second': True}) == {'r': 14}
    stopped = entry.run('source-stop', {'x': 7, 'first': False, 'second': False},
                        refuses='entry-run-incomplete')
    assert stopped['execution']['roles'][0]['before'][1]['cause'] == [
        'explicit', {'omitted_bytes': 0, 'text': 'reject'},
    ]
    assert 'rejected:require' not in str(stopped)
    failed = entry.run('raw-failure', {'x': 7, 'first': True, 'second': False},
                       refuses='entry-run-incomplete')
    assert 'rejected:require' in str(failed)
    assert failed['execution']['roles'][0]['before'][1]['cause'][0] == 'backend'


@pytest.mark.parametrize('owner', ['P', 'V'])
@pytest.mark.parametrize('local', [False, True])
def test_require_in_shared_loop_preserves_stop_prefix(toolchain, journal, directory, owner, local):
    condition = 'checked(go)' if local else 'go'
    source = f'''module sample;
fn checked(go:bool)->bool{{require go;return go;}}
protocol Run roles(P,V)(n:index@(P,V),go:bool@{owner})->(r:bool@V){{
  for _ in 0..n roles(P,V) max 2{{
    require {condition};
    let actual=send P->V(true);
  }}
  return true;
}}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source)
    def roles(n, go):
        result = {role: {'inputs': {'n': n}} for role in ('P', 'V')}
        result[owner]['inputs']['go'] = go
        return result
    assert entry.run_roles('zero', roles(0, False))['V'] == {'r': True}
    assert entry.run_roles('pass', roles(1, True))['V'] == {'r': True}
    report = entry.run_roles('stop', roles(1, False), refuses='entry-run-incomplete')
    stopped = next(role for role in report['execution']['roles'] if role['role'] == owner)
    assert stopped['before'][1]['cause'] == ['explicit', {'omitted_bytes': 0, 'text': 'reject'}]
    assert 'loop-count-disagreement' not in str(report)
    assert 'provenance' not in str(report)


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_nested_calls_preserve_draw_and_rejection_order(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("bls12-381.fr");
fn checked(x:F,go:bool)->F{require go;return x;}
fn add(a:F,b:F)->F{return a+b;}
protocol Run roles(P)(go:bool@P, coins:Random<F>@P)->(r:F@P){
  return add(checked(coins.draw(),go),coins.draw());
}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    report = entry.run_roles('stop-after-first-draw', {'P': {'inputs': {'go': False}, 'services': {'coins': 1}}},
                             refuses='entry-run-incomplete')
    assert report['execution']['roles'][0]['before'][1]['cause'] == [
        'explicit', {'omitted_bytes': 0, 'text': 'reject'},
    ]
    # The first draw consumed the available budget. Reaching the second draw
    # would report exhaustion, so the source stop must precede it.
    assert 'exhausted' not in str(report)
    report = entry.run_roles('second-draw-exhausts', {'P': {'inputs': {'go': True}, 'services': {'coins': 1}}},
                             refuses='entry-run-incomplete')
    assert 'exhausted' in str(report)
