"""Programmable construction ABI and state-chain execution through the Host.

Toy providers exercise state and event correspondence; cryptographic fixtures
compare concrete histories and malformed-input order. Neither establishes
cryptographic security or complete external-parser equivalence.
"""
import copy
import hashlib
import json

import pytest
from source_modules import library_modules

SOURCE = '''module sample;
domain F=field("bls12-381.fr");
interface TestTranscript<T:Field> {
  type State:Copy+Drop;
  fn initialize()->State effects(stop, opaque);
  fn observe(t:State,v:T)->State effects(stop, opaque);
  fn draw(t:State)->(State,T) effects(stop, opaque);
}
protocol Round<T:Field> roles(P,V)
    (public:T@(P,V),rounds:index@(P,V),secret:T@P,challenges:Random<T>@V)->(ok:bool@V){
  let mut accepted@V=true;
  LOOP_START
  #[site(commitment)] let first=send P->V((secret,secret));
  #[site(challenge)] let c=challenges.draw();
  #[site(delivery)] let actual=send V->P(c);
  #[site(response)] let last=send P->V((secret+actual,secret));
  accepted=last.0==first.0+c;
  LOOP_END
  return accepted;
}
construction Derived<T:Field,H:TestTranscript<T>> for Round<T>{
  transcript H;
  replace challenges;
  on start(t,public){return H::observe(t,public);}
  on message {commitment,response}(t,value){return H::observe(t,value.0);}
  on message delivery(t,value){return t;}
  on query challenge(t){return H::draw(t);}
}
module Provider:TestTranscript<F>{
  type State:Copy+Drop=STATE;
  fn initialize()->State{return State(INITIAL);}
  fn observe(t:State,v:F)->State{return t;}
  fn draw(t:State)->(State,F){return(t,1);}
}
proof Demo=Round<F>{prover P;verifier V;public{public,rounds};accept ok;
  construction Derived<F,Provider>;}
'''


@pytest.mark.parametrize('slots', [0, 2])
@pytest.mark.parametrize('nested', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_custom_construction_state_and_logical_payloads(toolchain, journal, directory, slots, nested, flags):
    source = directory / 'main.zkc'
    text = SOURCE
    if slots == 2 and not nested:
        # Reusing the factory as ordinary protocol code creates unrelated data,
        # not a second construction root or a reset of its current state.
        text = text.replace('  let mut accepted@V=true;',
                            '  let spare@P=Provider::initialize();\n  let mut accepted@V=true;')
    source.write_text(text.replace('STATE', '()' if slots == 0 else '(index,index)')
                     .replace('INITIAL', '()' if slots == 0 else '(0,0)')
                     .replace('LOOP_START', 'for _ in 0..rounds roles(P,V) max 2 {\n' * 2 if nested else '')
                     .replace('LOOP_END', '}}' if nested else ''))
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile',
                             f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                             'sample::Demo', f'--output={package}', *flags])
    public = journal.write('public.json', {'public': '5', 'rounds': '2'})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}']
    proof = directory / 'proof.bin'
    if not flags:
        journal.json([toolchain.runtime, '--json', 'prove', *args,
                      f'--witness={witness}', f'--output={proof}'], refuses='entry-proof-binding-policy')
    args.append('--allow-authored')
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                             f'--witness={witness}', f'--output={proof}'])
    assert produced['binding_scope'] == 'header'
    verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert verified['status'] == 'accepted'
    assert not verified['execution']['cleanup_errors']
    if slots == 2 and not nested and not flags:
        check_construction_mutations(toolchain, journal, directory, package)
    if nested:
        empty_public = journal.write('empty-public.json', {'public': '5', 'rounds': '0'})
        empty_args = [x for x in args if not x.startswith('--public=')] + [f'--public={empty_public}']
        empty = directory / 'empty.bin'
        journal.json([toolchain.runtime, '--json', 'prove', *empty_args,
                      f'--witness={witness}', f'--output={empty}'])
        assert journal.json([toolchain.runtime, '--json', 'verify', *empty_args,
                              f'--proof={empty}'])['status'] == 'accepted'


@pytest.mark.parametrize('out_of_range', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_custom_index_query_keeps_the_service_range(toolchain, journal, directory, out_of_range, flags):
    source = directory / 'main.zkc'
    source.write_text('''module sample;
    domain F=field("koala-bear.ext8-binomial3");
    interface ProviderType {type State:Copy+Drop;fn initialize()->State effects(stop, opaque);}
    module Provider:ProviderType {
      type State:Copy+Drop=();
      fn initialize()->State{return State(());}
    }
    protocol Choose roles(P,V)(challenges:Random<F>@V)->(ok:bool@V) {
      #[site(pick)] let choice=challenges.index<8>();
      #[site(delivery)] let actual=send V->P(choice);
      return true;
    }
    construction Custom<H:ProviderType> for Choose {
      transcript H;replace challenges;
      on start(t){return t;}
      on query pick(t,bound){return (t,RESULT);}
      on message delivery(t,value){return t;}
    }
    proof Demo=Choose {prover P;verifier V;public{};accept ok;construction Custom<Provider>;}
    '''.replace('RESULT', 'bound' if out_of_range else '0'))
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Demo', f'--output={package}', *flags])
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', '--allow-authored']
    proof = directory / 'proof.bin'
    result = journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'],
                          refuses='rejected:require' if out_of_range else None)
    assert not result['execution']['cleanup_errors']
    if out_of_range:
        assert not proof.exists()
    else:
        assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                              f'--proof={proof}'])['status'] == 'accepted'
        if not flags:
            deployed = json.loads(json.loads(package.read_text())['artifact'])
            for name, reason in [('missing-range', 'native-proof-index-range'),
                                 ('wrong-bound', 'native-proof-index-bound')]:
                changed = copy.deepcopy(deployed)
                program = json.loads(changed[4])
                bindings = {row[0]: row[1] for row in program[1]}
                handler = next(f for f in program[2] if f[1] == changed[2][6][6][0][0])
                if name == 'missing-range':
                    handler[4] = [op for op in handler[4]
                                  if not (op[0] == 'op' and bindings[op[2]] == 'control.require')]
                else:
                    bound = next(op for op in handler[4]
                                 if op[0] == 'op' and bindings[op[2]] == 'index.constant' and op[3] == ['8'])
                    bound[3] = ['16']
                changed[4] = json.dumps(program)
                reject_deployment(toolchain, journal, directory, changed, name, reason)


def reject_deployment(toolchain, journal, directory, deployment, name, reason):
    def frame(value):
        if isinstance(value, str):
            encoded = value.encode()
            return bytes([0]) + len(encoded).to_bytes(8, 'little') + encoded
        return bytes([1]) + len(value).to_bytes(8, 'little') + b''.join(map(frame, value))
    deployment[3] = hashlib.sha256(frame(deployment[2])).hexdigest()
    deployment[5] = hashlib.sha256(deployment[4].encode()).hexdigest()
    encoded = json.dumps(deployment).encode()
    path = directory / (name + '.deployment')
    path.write_bytes(encoded)
    inputs = journal.write(name + '.inputs.json', [])
    result = journal.json([toolchain.runtime, '--json', 'prove-bundle', path,
                           hashlib.sha256(encoded).hexdigest(), inputs,
                           directory / (name + '.bin'), '--allow-authored'], refuses=reason)
    assert result['phase'] == 'admission'


def check_construction_mutations(toolchain, journal, directory, package):
    deployed = json.loads(json.loads(package.read_text())['artifact'])
    candidate = json.loads(deployed[4])
    plan = deployed[2][6]
    for name, reason in [('state', 'native-proof-state-chain'),
                         ('payload', 'native-proof-observation-payload'),
                         ('start', 'native-proof-construction-root'),
                         ('coverage', 'native-proof-construction-coverage'),
                         ('selector', 'native-proof-construction')]:
        changed = copy.deepcopy(deployed)
        program = copy.deepcopy(candidate)
        if name in ('state', 'payload'):
            producer = program[3][0]
            body = producer[6]
            observed = next(op for op in body if op[0] == 'local' and op[2] == plan[6][0][0])
            if name == 'state':
                observed[3][0] = body[0][4][0]  # Bypass start while retaining the index type.
            else:
                observed[3][2] = producer[4][0][0]  # Public data instead of the actual send.
            changed[4] = json.dumps(program)
        elif name == 'start':
            changed[2][6][5][1] = ['2']  # A prover-private input cannot initialize both roles.
        elif name == 'coverage':
            changed[2][6][6][0][2].reverse()
        else:
            changed[2][6][1] = 'different'
        reject_deployment(toolchain, journal, directory, changed, name, reason)


@pytest.mark.parametrize('override', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_native_base_supports_ordinary_affine_handlers(toolchain, journal, directory, override, flags):
    # A no-op observation is deliberately different from the native baseline.
    # The managed root still binds the selected deployment and public inputs.
    source = directory / 'main.zkc'
    text = SOURCE[:SOURCE.index('construction Derived')]
    text = text.replace('LOOP_START', 'for _ in 0..rounds roles(P,V) max 2 {')
    text = text.replace('LOOP_END', '}')
    text += '''construction Native<T:Field> for Round<T> {
      base fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);
      HANDLERS
    }
    proof Demo=Round<F>{prover P;verifier V;public{public,rounds};accept ok;
      construction Native<F>;}
    '''.replace('HANDLERS', '''on start(t,public){return t;}
      on message commitment(t,value){return t;}''' if override else '')
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Demo', f'--output={package}', *flags])
    public = journal.write('public.json', {'public': '5', 'rounds': '2'})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}']
    proof = directory / 'proof.bin'
    assert journal.json([toolchain.runtime, '--json', 'prove', *args,
                         f'--witness={witness}', f'--output={proof}'])['binding_scope'] == 'transcript'
    assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                         f'--proof={proof}'])['status'] == 'accepted'
    if override and not flags:
        deployment = json.loads(json.loads(package.read_text())['artifact'])
        plan = deployment[2][6]
        original = json.loads(deployment[4])
        native_names = {row[0] for row in plan[6] if row[1] == 'native'}
        native = next(f for f in original[2] if f[1] in native_names and len(f[3]) == 1)
        custom = next(row[0] for row in plan[6] if row[1] == 'local')
        for destination in (custom, plan[5][0], 'stray_native'):
            changed = copy.deepcopy(deployment)
            program = copy.deepcopy(original)
            replacement = copy.deepcopy(native)
            replacement[1] = destination
            target = next((f for f in program[2] if f[1] == destination), None)
            if target:
                # Keep the existing callable signature so ordinary admission
                # succeeds before the construction-specific authority check.
                names = {replacement[2][0][0]: target[2][0][0],
                         replacement[2][1][0]: target[2][1][0]}
                coordinate = replacement[2][-1][0]
                if target[2][-1][1].startswith('index@'):
                    names[coordinate] = target[2][-1][0]
                else:
                    program[1].append(['zero_index', 'index.constant', [], 'native/index.constant'])
                    replacement[4].insert(0, ['op', 'zero_coordinate', 'zero_index',
                                              ['0'], [], [coordinate]])
                def rename(value):
                    if isinstance(value, list):
                        return [rename(item) for item in value]
                    return names.get(value, value)
                replacement[4] = rename(replacement[4])
                replacement[2] = target[2]
            program[2] = [f for f in program[2] if f[1] != destination] + [replacement]
            changed[4] = json.dumps(program)
            reject_deployment(toolchain, journal, directory, changed, destination,
                              'native-proof-transcript-operation')


@pytest.mark.parametrize('protocol', ['schnorr', 'sumcheck'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage', '--fuse-vector-reductions']])
def test_source_construction_cryptographic_histories(toolchain, journal, directory, protocol, flags):
    from pathlib import Path
    from test_source_transcript import PUBLIC, VECTOR
    root = Path(__file__).resolve().parents[3]
    modules = {'sample': root / f'common/tests/fixtures/constructions/{protocol}.zkc',
               'spongefish': root / 'libraries/spongefish/lib.zkc'}
    modules.update({f'zkc::{name}': root / f'libraries/zkc/{name}.zkc'
                    for name in ['multilinear', 'bytes', 'shake128', 'encoding', 'vector', 'boolean', 'finite', 'sequence', 'accumulation', 'curve']})
    if protocol == 'sumcheck':
        modules['sumcheck'] = root / 'libraries/sumcheck/lib.zkc'
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             *library_modules('spongefish', 'sumcheck', overrides=modules),
                             'sample::Demo', f'--output={package}', *flags])
    public_value = PUBLIC if protocol == 'schnorr' else {
        'values': ['1', '2', '3', '4'], 'claim': '10', 'rounds': '2'}
    public = journal.write('public.json', public_value)
    witness = journal.write('witness.json', {'scalar': '7', 'nonce': '11'} if protocol == 'schnorr' else {})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}',
            '--allow-authored']
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                             f'--witness={witness}', f'--output={proof}'])
    verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert verified['status'] == 'accepted'
    assert not verified['execution']['cleanup_errors']
    if protocol == 'schnorr':
        framed = proof.read_bytes()
        # Native framing has a 40-byte header and a length plus six-byte codec
        # tag per message. Its scalar codec is little endian. The mathematical
        # messages exactly match the independently generated external vector.
        assert len(framed) == 148
        assert framed[54:102] == VECTOR[:48]
        assert framed[-32:][::-1] == VECTOR[48:]
        # The empty provider factory adds one work unit before on start.
        assert produced['execution']['external_work'] == 842
        assert verified['execution']['external_work'] == 842
    else:
        assert produced['execution']['messages'] == 4
        candidate = bytearray(proof.read_bytes())
        candidate[54] ^= 1  # First round field, before V's require and draw.
        invalid = directory / 'invalid.bin'
        invalid.write_bytes(candidate)
        rejected = journal.json([toolchain.runtime, '--json', 'verify', *args,
                                 f'--proof={invalid}'], refuses='artifact-stopped')
        assert rejected['execution']['external_work'] < verified['execution']['external_work']
        assert not rejected['execution']['cleanup_errors']


@pytest.mark.parametrize('suite', ['merlin3.bls12-381.fr64be/0', 'spongefish0.8.0.keccak.bls12-381.fr64be/0',
                                   'hash-chain.keccak256.bls12-381.fr64be/0'])
@pytest.mark.parametrize('flags', [[], ['--release-storage']])
def test_managed_provider_methods_are_ordinary_checked_functions(toolchain, journal, directory, suite, flags):
    from pathlib import Path
    root = Path(__file__).resolve().parents[3]
    source = directory / 'main.zkc'
    source.write_text((root / 'common/tests/fixtures/constructions/managed.zkc').read_text()
                      .replace('merlin3.bls12-381.fr64be/0', suite))
    modules = {'sample': source}
    modules.update({f'zkc::{name}': root / f'libraries/zkc/{name}.zkc'
                    for name in ['bytes', 'encoding', 'transcript']})
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             *library_modules('spongefish', 'sumcheck', overrides=modules),
                             'sample::Demo', f'--output={package}', *flags])
    public = journal.write('public.json', {'public': '5'})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}']
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                             f'--witness={witness}', f'--output={proof}'])
    assert produced['binding_scope'] == 'transcript'
    accepted = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert accepted['status'] == 'accepted'
    assert not accepted['execution']['cleanup_errors']


@pytest.mark.parametrize('suite', ['merlin3.koala-bear.ext8-binomial3.rejection31le/0',
                                   'hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0'])
@pytest.mark.parametrize('bound', [0, 3, 8, 9223372036854775809])
def test_managed_index_methods_reject_invalid_bounds_and_clean_up(toolchain, journal, directory, suite, bound):
    from pathlib import Path
    root = Path(__file__).resolve().parents[3]
    source = directory / 'main.zkc'
    source.write_text('''module sample;
    use zkc::transcript as history;
    use zkc::bytes as bytes;
    domain F=field("koala-bear.ext8-binomial3");
    domain T=transcript("SUITE");
    protocol Choose roles(P,V)(challenges:Random<F>@V)->(ok:bool@V){
      #[site(pick)] let choice=challenges.index<8>();
      #[site(delivery)] let actual=send V->P(choice);
      return true;
    }
    construction Custom for Choose {
      transcript T;replace challenges;
      on start(t){return t;}
      on query pick(t,bound){return history::challenge_index(t,bytes::empty(),BOUND);}
      on message delivery(t,value){return t;}
    }
    proof Demo=Choose{prover P;verifier V;public{};accept ok;construction Custom;}
    '''.replace('BOUND', str(bound)).replace('SUITE', suite))
    package = directory / 'proof.zkpkg'
    modules = {'sample': source, 'zkc::transcript': root / 'libraries/zkc/transcript.zkc',
               'zkc::bytes': root / 'libraries/zkc/bytes.zkc'}
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             *library_modules('spongefish', 'sumcheck', overrides=modules),
                             'sample::Demo', f'--output={package}'])
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}']
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'],
                             refuses='query-bound' if bound != 8 else None)
    assert not produced['execution']['cleanup_errors']
    if bound == 8:
        assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                              f'--proof={proof}'])['status'] == 'accepted'
    else:
        assert not proof.exists()

@pytest.mark.parametrize('slots', [0, 2])
@pytest.mark.parametrize('flags', [[], ['--release-storage']])
def test_copyable_construction_state_survives_untaken_completion(toolchain, journal, directory, slots, flags):
    source = directory / 'main.zkc'
    text = SOURCE.replace('STATE', '()' if slots == 0 else '(index,index)').replace('INITIAL', '()' if slots == 0 else '(0,0)')
    text = text.replace('LOOP_START', '').replace('LOOP_END', '')
    text = text.replace('public:T@(P,V),', 'go:bool@(P,V),public:T@(P,V),')
    text = text.replace('->(ok:bool@V){', '->(ok:bool@V) completes{')
    text = text.replace('let first=send P->V((secret,secret));', 'let first=send P->V((secret,secret));\n'
                        'let ()=finish_if @P(go)();let _=finish_if @V(go)(ok=true);')
    text = text.replace('public{public,rounds}', 'public{go,public,rounds}')
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Demo', f'--output={package}', *flags])
    public = journal.write('public.json', {})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}', '--allow-authored']
    proof = directory / 'proof.bin'
    for go in (False, True):
        public.write_text(json.dumps({'go': go, 'public': '5', 'rounds': '2'}))
        journal.json([toolchain.runtime, '--json', 'prove', *args,
                      f'--witness={witness}', f'--output={proof}'])
        assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                             f'--proof={proof}'])['status'] == 'accepted'


@pytest.mark.parametrize('mutation', ['ordinary-call', 'send', 'output', 'capture', 'carried'])
def test_copyable_construction_state_is_internal(toolchain, journal, directory, mutation):
    text = SOURCE.replace('STATE', 'bool' if mutation == 'output' else 'F')
    text = text.replace('INITIAL', 'false' if mutation == 'output' else '0')
    source = directory / 'main.zkc'
    source.write_text(text.replace('LOOP_START', '').replace('LOOP_END', ''))
    package = directory / 'proof.zkpkg'
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', 'sample::Demo', f'--output={package}'])
    deployment = json.loads(json.loads(package.read_text())['artifact'])
    program = json.loads(deployment[4])
    producer = program[3][1 if mutation == 'output' else 0]
    body = producer[6]
    state = body[1][4][0]  # The start handler's actual current state.
    state_type = producer[5][-1]
    if mutation == 'ordinary-call':
        program[2].append(['function', 'leak', [['input', state_type]], [],
                           [['return', []]], ['leak', []]])
        body.insert(2, ['local', 'leak', 'leak', [state], []])
    elif mutation == 'send':
        next(op for op in body if op[0] == 'send')[4] = state
    elif mutation == 'output':
        body[-1][1][0] = state
    else:
        rounds = producer[4][1][0]
        carried = [['state_copy', state]] if mutation == 'carried' else []
        captures = [state] if mutation == 'capture' else []
        yielded = ['state_copy'] if carried else []
        outputs = ['leaked_state'] if carried else []
        body.insert(2, ['loop', 'leak', ['value', rounds, '2', 'iteration'],
                        carried, captures, [['yield', yielded]], outputs])
    deployment[4] = json.dumps(program)
    reject_deployment(toolchain, journal, directory, deployment, mutation, 'native-proof-state-escape')
