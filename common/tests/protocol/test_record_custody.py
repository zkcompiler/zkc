"""Restricted record custody through source, native loops and the common Host."""
import pytest

from entry import Entry


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_exact_record_successors_and_zero_trip_stops(toolchain, journal, directory, flags):
    source = '''module sample;
#[linear] struct State<N:nat>{value:bool,empty:(),phantom:[bool;0]}
#[linear] struct Empty{}
fn make()->State<7>{return State<7>{value:true,empty:(),phantom:[]};}
fn make_empty()->Empty{return Empty{};}
fn advance(x:State<7>,go:bool)->State<7>{
 let opened=inspect_record(x);
 return if go{repack_record(opened.0,(!opened.1.0,(),[]))}else{stop "reject";};
}
fn forward_empty(x:Empty)->Empty{return repack_record(x,());}
fn local_loop(x:State<7>,n:index,go:bool)->State<7>{
 let mut current=x;
 for _ in 0..n{current=advance(current,go);}
 return current;
}
fn finish(x:State<7>)->bool{let fields=unpack(x);return fields.0;}
fn finish_empty(x:Empty)->(){consume x;return ();}
protocol Run roles(P)(n:index@P,inner:index@P,go:bool@P)->(result:bool@P){
 let mut current@P=make();let mut empty@P=make_empty();
 for _ in 0..n roles(P) max 3{
  let next@P=local_loop(current,inner,go);current=next;
  let next_empty@P=forward_empty(empty);empty=next_empty;
 }
 let done@P=finish_empty(empty);return finish(current);
}
entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for outer, inner in [(0, 3), (1, 0), (1, 1), (2, 1), (3, 3)]:
        result = entry.run(f'counts-{outer}-{inner}',
                           {'n': str(outer), 'inner': str(inner), 'go': True})
        assert result['result'] is (outer * inner % 2 == 0)
    for outer, inner in [(0, 3), (2, 0)]:
        assert entry.run(f'skipped-{outer}-{inner}',
                         {'n': str(outer), 'inner': str(inner), 'go': False})['result']
    entry.run('reached-stop', {'n': '1', 'inner': '1', 'go': False},
              refuses='entry-host-run-failed')
