"""Programmable construction ABI and state-chain execution through the Host.

The toy provider returns a constant challenge. These are correspondence tests,
not cryptographic security tests or an external transcript implementation.
"""
import copy
import hashlib
import json

import pytest

SOURCE = '''module sample;
domain F=field("bls12-381.fr");
interface TestTranscript<T:Field> {
  type State:Copy+Drop;
  fn initialize()->State;
  fn observe(t:State,v:T)->State;
  fn draw(t:State)->(State,T);
}
protocol Round<T:Field+Share+Wire> roles(P,V)
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
construction Derived<T:Field+Share+Wire,H:TestTranscript<T>> for Round<T>{
  transcript H;
  replace challenges;
  on start(t,public){return H::observe(t,public);}
  on message {commitment,response}(t,value){return H::observe(t,value.0);}
  on message delivery(t,value){return t;}
  on query challenge(t){return H::draw(t);}
}
component Provider:TestTranscript<F>{
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
    interface ProviderType {type State:Copy+Drop;fn initialize()->State;}
    component Provider:ProviderType {
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
