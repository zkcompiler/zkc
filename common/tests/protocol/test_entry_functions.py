"""Source Entry functions share native calculation, proof and cumulative policy."""
import json

import pytest

from input_files import input_files


def compile_function(toolchain, journal, directory, source, entry='Main', flags=()):
    path = directory / 'entry.zkc'
    path.write_text(source)
    package = directory / f'{entry}.zkpkg'
    built = journal.json([toolchain.runtime, '--json', 'compile',
                          f'--compiler={toolchain.compiler}', f'--module=example={path}',
                          f'example::{entry}', f'--output={package}', *flags])
    return package, built['package_sha256']


def execute(toolchain, journal, directory, package, pin, name, arguments, *,
            flags=(), refuses=None):
    inputs = input_files(journal, name, arguments=arguments, package=package)
    output = directory / f'{name}.results.json'
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={pin}', *inputs, f'--results={output}', *flags],
                          refuses=refuses)
    if refuses:
        assert report['status'] == 'refused'
        assert not output.exists(), 'a failed source return was published'
        return report, None
    assert report['status'] == 'executed' and report['execution']['completed']
    result = json.loads(output.read_text())
    assert result.keys() == {'format', 'value'}
    assert result['format'] == 'zkc.entry-outputs/0'
    return report, result['value']


CALCULATION = '''module example;
domain F=field("koala-bear");
math fn square(x:F)->F{return x*x;}
fn shifted(x:F)->F{return square(x)+1;}
entry fn Step(x:F)->F{return shifted(x);}
entry fn Main(x:F,count:index,enabled:bool)->F{
  let mut result=x;
  if enabled {for _ in 0..count {result=Step(result);}}
  return result;
}
'''


@pytest.mark.parametrize('flags', [(), ('--no-simplify',), ('--release-storage',)])
def test_standalone_calculation_static_calls_and_reached_control(toolchain, journal, directory, flags):
    package, pin = compile_function(toolchain, journal, directory, CALCULATION, flags=flags)
    artifact = json.loads(json.loads(package.read_text())['artifact'])
    assert artifact['deployments'] == []
    assert artifact['calculations']
    assert all('function' in calculation and 'participant' not in calculation
               for calculation in artifact['calculations'])
    for name, enabled, count, expected in [('skipped', False, 100, 2),
                                          ('empty', True, 0, 2), ('composed', True, 2, 26)]:
        report, value = execute(toolchain, journal, directory, package, pin, name,
                                {'x': '2', 'count': count, 'enabled': enabled})
        assert value == str(expected)
        operations = [call['operation'] for call in report['execution']['calls']]
        assert operations.count('entry') == (count if enabled else 0)
        if enabled and count > 0:
            assert 'numeric' in operations
        assert report['execution']['failure'] is None


def test_false_is_data_and_require_retains_a_failed_call_prefix(toolchain, journal, directory):
    source = '''module example;
entry fn Checked(go:bool)->bool{require go;return go;}
entry fn Main(go:bool,check:bool)->bool{
  return if check {Checked(go)} else {go};
}
'''
    package, pin = compile_function(toolchain, journal, directory, source)
    report, value = execute(toolchain, journal, directory, package, pin, 'false',
                            {'go': False, 'check': False})
    assert value is False and report['execution']['calls'] == []
    failed, value = execute(toolchain, journal, directory, package, pin, 'require',
                            {'go': False, 'check': True}, refuses='entry-host-require')
    assert value is None and not failed['execution']['completed']
    assert failed['execution']['failure']['path']
    calls = failed['execution']['calls']
    assert len(calls) == 1 and calls[0]['operation'] == 'entry' and not calls[0]['completed']


@pytest.mark.parametrize('numeric', [False, True])
def test_cumulative_instruction_budget_does_not_reset_at_entry_calls(toolchain, journal, directory, numeric):
    source = '''module example;
entry fn Step(x:bool)->bool{return x;}
entry fn Main(x:bool,count:index)->bool{
  let mut result=x;
  for _ in 0..count {result=Step(result);}
  return result;
}
'''
    if numeric:
        source = CALCULATION
    package, pin = compile_function(toolchain, journal, directory, source)
    def arguments(count):
        return {'x': '2', 'count': count, 'enabled': True} if numeric else {'x': True, 'count': count}

    once, value = execute(toolchain, journal, directory, package, pin, 'one', arguments(1))
    assert value == ('5' if numeric else True)
    repeated, value = execute(toolchain, journal, directory, package, pin, 'many', arguments(8))
    expected = 2
    for _ in range(8):
        expected = (expected * expected + 1) % 2130706433
    assert value == (str(expected) if numeric else True)
    low, high = (r['execution']['usage']['instructions'] for r in (once, repeated))
    assert low < high
    ceiling = (low + high) // 2
    capacity = journal.write('cumulative.capacity.json', [
        'zkc.native-capacity/0', '65536', '4096', '16777216', '67108864',
        [str(ceiling), '100000', '4294967296'], ['67108864', '268435456']])
    flags = [f'--capacity={capacity}']
    _, value = execute(toolchain, journal, directory, package, pin, 'bounded-one',
                       arguments(1), flags=flags)
    assert value == ('5' if numeric else True)
    refused, _ = execute(toolchain, journal, directory, package, pin, 'bounded-many',
                          arguments(8), flags=flags, refuses=True)
    assert refused['code'] in {'Limit', 'entry-host-numeric-stopped'}
    usage = refused['execution']['usage']
    assert usage['instructions'] <= ceiling
    calls = refused['execution']['calls']
    assert any(call['completed'] for call in calls)
    assert sum(call['operation'] == 'entry' for call in calls) < 8
    assert refused['execution']['failure']['path']
    if refused['code'] == 'entry-host-numeric-stopped':
        stopped = refused['execution']['failure']['native']['stop']
        assert stopped['kind'] == 'Limit' and not stopped['cleanup_errors']


PROOF = '''module example;
protocol Check roles(P,V)(expected:bool@(P,V),candidate:bool@P)->(value:bool@P,accepted:bool@V){
  let received=send P->V(candidate);
  let accepted@V=received==expected;
  return(value=candidate,accepted=accepted);
}
proof Family=Check{prover P;verifier V;public{expected};accept accepted;construction authored;}
entry fn Produce(public:Family::Public,witness:Family::Witness){return Family::prove(public,witness);}
entry fn Verify(public:Family::Public,candidate:Family::Proof){return Family::verify(public,candidate);}
'''


def test_independent_generated_proof_operations_and_semantic_rejection(toolchain, journal, directory):
    producer, producer_pin = compile_function(toolchain, journal, directory, PROOF, 'Produce')
    verifier, verifier_pin = compile_function(toolchain, journal, directory, PROOF, 'Verify')
    artifacts = [json.loads(json.loads(p.read_text())['artifact']) for p in (producer, verifier)]
    assert [d['operation'] for d in artifacts[0]['deployments']] == ['prove']
    assert [d['operation'] for d in artifacts[1]['deployments']] == ['verify']
    report, produced = execute(toolchain, journal, directory, producer, producer_pin, 'produce',
                               {'public': {'expected': True}, 'witness': {'candidate': True}},
                               flags=['--allow-authored'])
    assert produced['outputs'] == {'value': True}
    assert produced['proof']
    report, verified = execute(toolchain, journal, directory, verifier, verifier_pin, 'accept',
                                {'public': {'expected': True}, 'candidate': produced['proof']},
                                flags=['--allow-authored'])
    assert verified == {'case': 'Accepted', 'fields': {'outputs': {'accepted': True}}}
    _, negative = execute(toolchain, journal, directory, producer, producer_pin, 'produce-negative',
                           {'public': {'expected': True}, 'witness': {'candidate': False}},
                           flags=['--allow-authored'])
    assert negative['outputs'] == {'value': False}
    report, rejected = execute(toolchain, journal, directory, verifier, verifier_pin, 'reject',
                                {'public': {'expected': True}, 'candidate': negative['proof']},
                                flags=['--allow-authored'])
    assert rejected == {'case': 'Rejected', 'fields': {}}
    assert report['execution']['failure'] is None
    assert [call['operation'] for call in report['execution']['calls']] == ['verify']
    assert report['execution']['calls'][0]['completed']
    malformed, _ = execute(toolchain, journal, directory, verifier, verifier_pin, 'wrong-public',
                             {'public': {'expected': False}, 'candidate': produced['proof']},
                             flags=['--allow-authored'], refuses='proof-header')
    assert not malformed['execution']['completed']
    assert malformed['execution']['calls'][0]['operation'] == 'verify'
    assert not malformed['execution']['calls'][0]['completed']


@pytest.mark.parametrize('body', [
    'return if go {stop "abort";} else {true};',
    'if go {for _ in 0..2 {stop "abort";}} return true;',
])
def test_nested_stops_preserve_structured_regions_and_withhold_results(toolchain, journal, directory, body):
    source = f'module example; entry fn Main(go:bool)->bool{{{body}}}'
    package, pin = compile_function(toolchain, journal, directory, source)
    _, value = execute(toolchain, journal, directory, package, pin, 'continue', {'go': False})
    assert value is True
    report, value = execute(toolchain, journal, directory, package, pin, 'stop', {'go': True},
                             refuses='entry-host-stop')
    assert value is None
    assert report['execution']['failure']['path']
    assert not report['execution']['completed']


@pytest.mark.parametrize('count', [0, 3])
def test_loop_state_packing_preserves_multiple_successors_and_invariants(toolchain, journal, directory, count):
    source = '''module example;
entry fn Step(x:index)->index{return x+1;}
entry fn Main(seed:index,count:index)->(index,index){
  let mut a=seed;
  let mut b=seed;
  for i in 0..count {a=Step(a);b=b+i+seed;}
  return(a,b);
}
'''
    package, pin = compile_function(toolchain, journal, directory, source)
    report, value = execute(toolchain, journal, directory, package, pin, 'multi',
                            {'seed': '2', 'count': str(count)})
    assert value == [str(2 + count), str(2 + 2 * count + count * (count - 1) // 2)]
    assert sum(call['operation'] == 'entry' for call in report['execution']['calls']) == count


@pytest.mark.parametrize('count', [0, 3])
def test_loop_without_state_keeps_reached_effects(toolchain, journal, directory, count):
    source = '''module example;
entry fn Check(go:bool)->(){require go;return ();}
entry fn Main(go:bool,count:index)->bool{
  for _ in 0..count {Check(go);}
  return true;
}
'''
    package, pin = compile_function(toolchain, journal, directory, source)
    report, value = execute(toolchain, journal, directory, package, pin, 'zero-state',
                            {'go': True, 'count': str(count)})
    assert value is True
    assert sum(call['operation'] == 'entry' for call in report['execution']['calls']) == count
