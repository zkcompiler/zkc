"""Real authored PIR -> physical participants -> NativeBackend, independently
admitted/replayed by Lean. Primitive replies are explicit trusted fixtures;
upstream archived challenge bytes are separate finite correspondence evidence.
"""
import copy
import hashlib
import json
import struct
from pathlib import Path

import pytest
from journal import Journal, names
from toolchain import Toolchain, records

ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = ROOT / 'examples/protocols'
FIXTURE = json.loads((ROOT / 'tests/fixtures/external-constructions.json').read_text())
ORACLES = {(name, tuple(args)): out for name, args, out in FIXTURE['oracles']}
MAGIC = 1514881876


def wire(kind, value):
    if kind == 'indices':
        data = b'ZKCV\x01\x20' + struct.pack('<I', len(value)) + b''.join(struct.pack('<Q', n) for n in value)
    else:
        data = b'ZKCV\x01\x1f' + struct.pack('<Q', value)
    return ['wire', data.hex()]


def compile_source(text, directory):
    tools = Toolchain()
    journal = Journal(directory)
    directory.mkdir(parents=True, exist_ok=True)
    source = directory / 'source.json'
    participants = directory / 'participants.json'
    source.write_text(journal.run([tools.compiler, 'protocol-source', '-'], text))
    participants.write_text(journal.run([tools.compiler, 'protocol-compile', '-'], text))
    check = journal.json([tools.checker('interactive-protocol'), '--check', source, participants])
    assert check[:2] == ['checked', 'generic-structural-correspondence'], check
    # The selected physical carrier contains primitive identities, not a hidden
    # callback for an entire proof or transcript schedule.
    assert 'native/external.' in participants.read_text()
    return tools, journal, source, participants


def native(compiled, ports, entry='main'):
    tools, journal, source, participants = compiled
    supplied = [[name, wire(kind, value)] for name, (kind, value) in ports.items()]
    inputs = journal.write('native-inputs.json', ['zkc.run/2', entry, 'external-bridge', [],
        [['Worker', [], supplied, []]], []])
    report = journal.json([tools.runtime, 'run-protocol', source, participants, inputs,
        tools.checker('interactive-protocol')])
    journal.write('native-result.json', report)
    return report


def reference(compiled, ports, entry='main', service=True):
    tools, journal, source, _ = compiled
    supplied = [[name, [kind, [str(n) for n in value] if kind == 'indices' else str(value)]]
                for name, (kind, value) in ports.items()]
    inputs = ['zkc.reference-inputs/1', entry, 'external-bridge', [['Worker', supplied]], [], [], []]
    # The interpreter reports exactly the missing cryptographic request. Fill
    # only that request from the frozen table; never supply whole-transition
    # replies or a precomputed final result to Lean.
    for _ in range(64):
        path = journal.write('reference-inputs.json', inputs)
        out = journal.json([tools.checker('interactive-protocol'), '--generic-reference', source, path])
        if out[3][0] != 'pending-primitive' or not service:
            journal.write('reference-result.json', out)
            return out
        request = out[4][-1][1]
        assert request[0] == 'zkc.external-primitive/1'
        response = ORACLES[(request[2], tuple(map(int, request[3])))]
        inputs[5].append([request, ['ok', list(map(str, response))]])
    raise AssertionError('unexpected primitive request count')


def output(report):
    assert report['outcome'][0] == 'returned', report
    return report['outcome'][1]['Worker']


def reference_values(report):
    assert report[3][0] == 'returned', report[3]
    return [[kind, [int(x) for x in value] if kind == 'indices' else int(value) if kind == 'index' else value == 'true']
            for kind, value in report[3][1]]


def chain_ports(case):
    return {key: ('indices', case[key]) for key in ['initial', 'commitments', 'messages', 'lengths']}


@pytest.mark.parametrize('case', FIXTURE['monero'], ids=lambda x: x['name'])
def test_archived_monero_compiled(case):
    compiled = compile_source((EXAMPLES / 'external-monero-schedule.pir').read_text(), records(case=case['name']))
    ports = chain_ports(case)
    result = output(native(compiled, ports))
    assert result == [['indices', [MAGIC, 1, 1] + case['state']], ['indices', case['challenges']]]
    if case['name'] == 'ordinary-monero-1':
        assert reference_values(reference(compiled, ports)) == result
        assert reference(compiled, ports, service=False)[3][:2] == ['pending-primitive', 'exact-request-missing']


@pytest.mark.parametrize('case', FIXTURE['openvm'][:5], ids=lambda x: x['name'])
def test_archived_openvm_compiled(case):
    compiled = compile_source((EXAMPLES / 'external-openvm-schedule.pir').read_text(), records(case=case['name']))
    events = case['events']
    ports = {'tags': ('indices', [int(e['sample']) for e in events]),
             'values': ('indices', [e['value'] for e in events])}
    result = output(native(compiled, ports))
    assert result == [['indices', case['final']], ['indices', [e['value'] for e in events if e['sample']]]]
    # Independent Lean schedule replay through the same authored loop. A finite
    # prefix bounds reference oracle calls, while native runs the whole archive.
    prefix = {name: (kind, xs[:64]) for name, (kind, xs) in ports.items()}
    assert reference_values(reference(compiled, prefix)) == output(native(compiled, prefix))


@pytest.mark.parametrize('bits', [0, 4])
def test_duplex_atomic_schedule(bits):
    compiled = compile_source((EXAMPLES / 'external-constructions.pir').read_text(), records(case=f'duplex-{bits}'))
    ports = {'observations': ('indices', [1, 2, 3]), 'bits': ('index', bits), 'witness': ('index', 5)}
    result = output(native(compiled, ports, 'openvm'))
    assert reference_values(reference(compiled, ports, 'openvm')) == result
    assert result[-1] == ['bool', True]
    if bits:
        assert result[4] == ['bool', False]
        assert result[0] != result[5]  # failed live witness still changes state
    else:
        assert result[4] == ['bool', True]
        assert result[0] == result[5]  # zero witness difficulty is no-op
        # sample_bits(0) consumed a sample (one + four + one = six).
        assert result[0][1][-1] == 2


def single_operation(contract, kinds, outputs):
    spell = {'indices': 'Indices', 'index': 'index', 'bool': 'bool'}
    args = ', '.join(f'x{i}: {spell[k]}' for i, k in enumerate(kinds))
    ins = ', '.join(f'x{i}' for i in range(len(kinds)))
    outs = ', '.join(f'y{i}' for i in range(len(outputs)))
    types = ', '.join(spell[k] for k in outputs)
    return f'''module {{
      fn Transition({args}) -> ({types}) {{
        let ({outs}) = {contract.replace('.', '::')}({ins});
        return ({outs});
      }}
      protocol Main {{ roles (Worker);
        inputs ({', '.join(f'Worker x{i}: {spell[k]}' for i,k in enumerate(kinds))});
        outputs ({', '.join('Worker '+spell[k] for k in outputs)});
        local [transition] Worker: let ({outs}) = Transition({ins});
        return ({outs});
      }}
      entry main = Main;
    }}'''


BAD_CASES = [
 ('external.monero.init', ['indices'], ['indices'], [[0]*31], 'external-word-width'),
 ('external.monero.init', ['indices'], ['indices'], [[256]+[0]*31], 'external-byte'),
 ('external.monero.hash', ['indices'], ['indices'], [[0]], 'external-word-width'),
 ('external.monero.update', ['indices','indices'], ['indices','indices'], [[MAGIC,1,2]+[0]*32, []], 'external-state-suite'),
 ('external.openvm.sample', ['indices'], ['indices','index'], [[MAGIC,1,2]+[0]*17], 'external-state-width'),
 ('external.openvm.sample', ['indices'], ['indices','index'], [[MAGIC,1,1]+[0]*18], 'external-state-suite'),
 ('external.openvm.sample', ['indices'], ['indices','index'], [[MAGIC,2,2]+[0]*18], 'external-state-suite'),
 ('external.openvm.sample', ['indices'], ['indices','index'], [[MAGIC,1,2]+[2013265921]+[0]*17], 'external-noncanonical-field'),
 ('external.openvm.sample', ['indices'], ['indices','index'], [[MAGIC,1,2]+[0]*16+[8,0]], 'external-state-index'),
 ('external.openvm.sample', ['indices'], ['indices','index'], [[MAGIC,1,2]+[0]*16+[0,9]], 'external-state-index'),
 ('external.openvm.observe', ['indices','indices'], ['indices'], [[MAGIC,1,2]+[0]*18, [2013265921]], 'external-noncanonical-field'),
 ('external.openvm.sample_bits', ['indices','index'], ['indices','index'], [[MAGIC,1,2]+[0]*18, 31], 'external-invalid-bit-width'),
 ('external.openvm.sample_bits', ['indices','index'], ['indices','index'], [[MAGIC,1,2]+[0]*18, 2**32], 'external-u32'),
 ('external.openvm.check_witness', ['indices','index','index'], ['indices','bool'], [[MAGIC,1,2]+[0]*18, 0, 2013265921], 'external-noncanonical-field'),
 # Multiple faults establish validation order, not merely acceptance equality.
 ('external.monero.update', ['indices','indices'], ['indices','indices'], [[MAGIC,1,1,256]+[0]*31, [256]], 'external-byte'),
 ('external.monero.update', ['indices','indices'], ['indices','indices'], [[MAGIC,1,1]+[0]*32, [256]], 'external-word-width'),
 ('external.openvm.check_witness', ['indices','index','index'], ['indices','bool'], [[MAGIC,1,2]+[0]*18, 31, 2013265921], 'external-invalid-bit-width'),
 ('external.openvm.check_witness', ['indices','index','index'], ['indices','bool'], [[MAGIC,1,2]+[0]*18, 31, 2**32], 'external-invalid-bit-width'),
 ('external.openvm.check_witness', ['indices','index','index'], ['indices','bool'], [[MAGIC,1,2]+[0]*16+[8,9], 31, 2013265921], 'external-state-index'),
]


@pytest.mark.parametrize('contract,kinds,outputs,values,code', BAD_CASES)
def test_canonical_refusals(contract, kinds, outputs, values, code):
    compiled = compile_source(single_operation(contract,kinds,outputs), records(case=f'{contract}-{code}-{values[0][-2:] if isinstance(values[0],list) else values[0]}'))
    ports = {f'x{i}': (kind,value) for i,(kind,value) in enumerate(zip(kinds,values))}
    report = native(compiled,ports)
    assert report['outcome'][0] == 'stopped', report
    assert names(json.dumps(report), 'refused:'+code), report
    ref = reference(compiled,ports,service=False)
    assert ref[3][0] == 'refused', ref[3]
    assert ref[3][1] == code


def test_explicit_grouping_changes_challenges():
    compiled = compile_source((EXAMPLES/'external-monero-schedule.pir').read_text(),records(case='grouping'))
    case = FIXTURE['monero'][0]
    correct = output(native(compiled,chain_ports(case)))
    changed = copy.deepcopy(case)
    # Replace the A update followed by the required empty update with one A
    # update. The later values change; serializing identical bytes is insufficient.
    assert changed['lengths'][1] == 0
    changed['lengths'].pop(1)
    altered = output(native(compiled,chain_ports(changed)))
    assert altered[0] != correct[0]
    split = copy.deepcopy(case)
    assert split['lengths'][-1] == 64
    split['lengths'][-1:] = [32, 32]
    assert output(native(compiled,chain_ports(split)))[0] != correct[0]


def test_uninstalled_suite_and_provider_rejected():
    compiled = compile_source(single_operation('external.openvm.sample',['indices'],['indices','index']),records(case='wrong-provider'))
    tools,journal,source,participants=compiled
    wrong = participants.read_text().replace('native/external.openvm.sample','dalek/external.openvm.sample')
    path=journal.directory/'wrong-provider.json';path.write_text(wrong)
    journal.run([tools.checker('interactive-protocol'),'--check',source,path],refuses='binding-implementation')
    text='''module { fn Wrong(t: Transcript<"openvm-babybear-poseidon2-v1">) -> Transcript<"openvm-babybear-poseidon2-v1"> { return t; } }'''
    journal.run([tools.compiler,'protocol-source','-'],text,refuses='source-name-unresolved')


def test_fixture_provenance():
    fixtures=ROOT/'tests/fixtures/external-transcript'
    for name,digest in FIXTURE['sources'].items():
        assert hashlib.sha256((fixtures/name).read_bytes()).hexdigest()==digest,name


@pytest.mark.parametrize('suite', ['monero-hash-chain-v1', 'openvm-babybear-poseidon2-v1'])
def test_external_suite_is_not_automatic_fiat_shamir(suite):
    tools=Toolchain()
    journal=Journal(records(case='automatic-'+suite))
    descriptor=(EXAMPLES/'dleq.construction.pir').read_text()
    descriptor=descriptor.replace('merlin3.bls12-381.fr64be/1',suite)
    path=journal.directory/'unsupported.construction.pir';path.write_text(descriptor)
    journal.run([tools.compiler,'protocol-construct',EXAMPLES/'dleq.pir',path],
                refuses='construction-suite-or-roles')


def test_external_operations_keep_failure_effects_and_reject_attributes():
    tools=Toolchain()
    journal=Journal(records(case='effects-and-attributes'))
    text=(EXAMPLES/'external-constructions.pir').read_text()
    ir=journal.run([tools.compiler,'protocol-import','-'],text)
    optimized=journal.run([tools.optimizer,'--canonicalize','--cse'],ir)
    for spelling in ['external_monero_hash','external_monero_update','external_openvm_check_witness']:
        assert optimized.count('"algebra.'+spelling+'"') == ir.count('"algebra.'+spelling+'"') > 0
    malformed=text.replace('external::monero::init(initial);',
                           'external::monero::init(initial) attributes ("prefix");')
    journal.run([tools.compiler,'protocol-source','-'],malformed,
                refuses='interactive-kernel-parameters')


def test_unused_external_validation_survives_standard_optimizations():
    text = '''module {
      fn Validate(x: Indices) -> index {
        let _ = external::monero::hash(x);
        return 7;
      }
      protocol Check {
        roles (Worker); inputs (Worker x: Indices); outputs (Worker index);
        local Worker: let result = Validate(x);
        return result;
      }
      entry main = Check;
    }'''
    tools = Toolchain()
    journal = Journal(records(case='unused-external-validation'))
    ir = journal.run([tools.compiler, 'protocol-import', '-'], text)
    optimized = journal.run([tools.optimizer, '--canonicalize', '--cse'], ir)
    assert optimized.count('"algebra.external_monero_hash"') == 1
    retained = journal.run([tools.compiler, 'protocol-export', '-'], optimized)
    compiled = compile_source(retained, journal.directory / 'retained')
    document = json.loads(compiled[2].read_text())
    port = document[3][0][4][0][0]  # Exported SSA binder, not the authored name.
    ports = {port: ('indices', [0])}  # Cannot be one complete hash word.
    actual = native(compiled, ports)
    assert actual['outcome'][0] == 'stopped'
    assert actual['stop']['detail'] == 'refused:external-word-width'
    expected = reference(compiled, ports, service=False)
    assert expected[3][:2] == ['refused', 'external-word-width']


def test_stateless_empty_hash_matches_monero_c_vector():
    compiled=compile_source(single_operation('external.monero.hash',['indices'],['indices']),records(case='empty-stateless'))
    ports={'x0': ('indices',[])}
    result=output(native(compiled,ports))
    expected=list(bytes.fromhex('4a078e76cd41a3d3b534b83dc6f2ea2de500b653ca82273b7bfad8045d85a400'))
    assert result==[['indices',expected]]
    assert reference_values(reference(compiled,ports))==result


def test_empty_duplex_observe_is_identity():
    compiled=compile_source(single_operation('external.openvm.observe',['indices','indices'],['indices']),records(case='empty-observe'))
    state=[MAGIC,1,2]+[0]*16+[0,3]
    ports={'x0': ('indices',state),'x1': ('indices',[])}
    result=output(native(compiled,ports))
    assert result==[['indices',state]]
    assert reference_values(reference(compiled,ports))==result


def test_wrong_primitive_reply_cannot_change_schedule():
    compiled=compile_source(single_operation('external.openvm.sample',['indices'],['indices','index']),records(case='wrong-primitive'))
    ports={'x0': ('indices',[MAGIC,1,2]+[0]*18)}
    pending=reference(compiled,ports,service=False)
    assert pending[3][0]=='pending-primitive'
    tools,journal,source,_=compiled
    request=pending[4][-1][1]
    inputs=json.loads((journal.directory/'reference-inputs.json').read_text())
    altered=copy.deepcopy(request);altered[3][0]='1'
    inputs[5]=[[altered,['ok',['0']*16]]]
    path=journal.write('reference-wrong-argument.json',inputs)
    out=journal.json([tools.checker('interactive-protocol'),'--generic-reference',source,path])
    assert out[3][:2]==['pending-primitive','exact-request-missing']
    inputs[5]=[[request,['ok',['2013265921']+['0']*15]]]
    path=journal.write('reference-noncanonical-reply.json',inputs)
    out=journal.json([tools.checker('interactive-protocol'),'--generic-reference',source,path])
    assert out[3][:2]==['refused','external-noncanonical-field']


def test_noncanonical_scalar_reply_is_refused():
    """A primitive reply at the scalar order is not a reduced Monero scalar."""
    compiled=compile_source(single_operation('external.monero.hash',['indices'],['indices']),records(case='noncanonical-scalar'))
    pending=reference(compiled,{'x0': ('indices',[0]*32)},service=False)
    assert pending[3][0]=='pending-primitive', pending[3]
    tools,journal,source,_=compiled
    request=pending[4][-1][1]
    inputs=json.loads((journal.directory/'reference-inputs.json').read_text())
    order=2**252+27742317777372353535851937790883648493
    inputs[5]=[[request,['ok',[str(b) for b in order.to_bytes(32,'little')]]]]
    path=journal.write('reference-noncanonical-scalar.json',inputs)
    out=journal.json([tools.checker('interactive-protocol'),'--generic-reference',source,path])
    assert out[3][:2]==['refused','external-noncanonical-scalar'], out[3]


@pytest.mark.parametrize('case', FIXTURE['openvm'][:5], ids=lambda x: x['name'])
def test_input_selected_external_schedule(case):
    compiled = compile_source((EXAMPLES / 'external-family.pir').read_text(),
                              records(case='family-' + case['name']))
    _, journal, source, participants = compiled
    frozen = source.read_bytes(), participants.read_bytes()
    fixed = compile_source((EXAMPLES / 'external-openvm-schedule.pir').read_text(),
                           journal.directory / 'fixed')
    for count in (0, 1, 9, 64):
        events = case['events'][:count]
        ports = {'tags': ('indices', [int(e['sample']) for e in events]),
                 'values': ('indices', [e['value'] for e in events])}
        result = output(native(compiled, ports))
        assert result == output(native(fixed, ports))
        assert reference_values(reference(compiled, ports)) == result
        assert (source.read_bytes(), participants.read_bytes()) == frozen
