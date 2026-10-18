"""Composed construction state, actual call arguments and root record coverage."""
import json
from pathlib import Path
import pytest
from source_modules import library_modules

from test_constructions import SOURCE, reject_deployment
from test_record_codecs import CODEC


def composed_source(empty, nested=False):
    text = SOURCE.replace('STATE', 'F').replace('INITIAL', '0')
    text = text.replace('LOOP_START', '').replace('LOOP_END', '')
    text = text.replace('fn observe(t:State,v:F)->State{return t;}',
                        'fn observe(t:State,v:F)->State{return State(unpack(t)*3+v);}')
    text = text.replace('fn draw(t:State)->(State,F){return(t,1);}',
                        'fn draw(t:State)->(State,F){return(State(unpack(t)+1),unpack(t));}')
    text += '''
    protocol Outer roles(P,V)
      (public:F@(P,V),rounds:index@(P,V),secret:F@P,challenges:Random<F>@V)->(ok:bool@V){
      let mut accepted@V=true;
      for _ in 0..rounds roles(P,V) max 2 {
        EMPTY_CALL
        #[site(step)] let result=Round<F> roles(P,V)(public+public,rounds,secret,challenges);
        accepted=result;
      }
      #[site(final_pick)] let final=challenges.draw();
      #[site(final_delivery)] let actual=send V->P(final);
      #[site(final_response)] let last=send P->V((actual,actual));
      return accepted;
    }
    construction Parent for Outer {
      transcript Provider;replace challenges;
      on start(t,public){return Provider::observe(t,public);}
      apply Derived<F,Provider> at step;
      EMPTY_SELECTION
      on query final_pick(t){return Provider::draw(t);}
      on message final_delivery(t,value){return t;}
      on message final_response(t,value){return Provider::observe(t,value.0);}
    }
    '''
    if empty:
        text = text.replace('EMPTY_CALL',
                            '#[site(empty)] let ignored=Empty roles(P,V)(public,challenges);'
                            '#[site(again)] let ignored=Empty roles(P,V)(public+public,challenges);')
        text = text.replace('EMPTY_SELECTION',
                            'apply EmptyConstruction at again;apply EmptyConstruction at empty;')
        text += '''
        protocol Empty roles(P,V)(public:F@(P,V),challenges:Random<F>@V)->(ok:bool@V){
          return true;
        }
        construction EmptyConstruction for Empty {
          transcript Provider;replace challenges;
          on start(t,public){return Provider::observe(t,public);}
        }
        '''
    else:
        text = text.replace('EMPTY_CALL', '').replace('EMPTY_SELECTION', '')
    if nested:
        text = text.replace('let result=Round<F> roles(P,V)', 'let result=Middle roles(P,V)')
        text = text.replace('apply Derived<F,Provider> at step;', 'apply MiddleConstruction at step;')
        text += '''
        protocol Middle roles(A,B)
          (public:F@(A,B),rounds:index@(A,B),secret:F@A,challenges:Random<F>@B)->(ok:bool@B){
          #[site(inner)] let ok=Round<F> roles(A,B)(public+public,rounds,secret,challenges);
          return ok;
        }
        construction MiddleConstruction for Middle {
          transcript Provider;replace challenges;
          on start(t,public){return Provider::observe(t,public);}
          apply Derived<F,Provider> at inner;
        }
        '''
    codec = CODEC.replace('for Round<F>', 'for Outer').replace('Packed=Round<F>', 'Packed=Outer')
    codec = codec.replace('BASE', 'base Parent;')
    codec = codec.replace('{commitment,response}', '{step.commitment,step.response,final_response}')
    if nested:
        codec = codec.replace('step.commitment', 'step.inner.commitment').replace(
            'step.response', 'step.inner.response')
    return text + codec


@pytest.mark.parametrize('empty', [False, True])
@pytest.mark.parametrize('nested', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage'],
                                   ['--no-finite-bulk'],
                                   ['--fuse-vector-reductions', '--no-simplify', '--release-storage']])
def test_child_state_arguments_and_root_codec(toolchain, journal, directory, empty, nested, flags):
    source = directory / 'main.zkc'
    # Exercise the shared mathematical selection policy inside a stateful
    # transcript helper. Summing three copies preserves the independent state
    # oracle below, whether the fold becomes a bulk kernel or stays a loop.
    source.write_text(composed_source(empty, nested).replace(
        'State(unpack(t)*3+v)',
        'State(zkc::finite::fold(zkc::vector::fill(unpack(t),3),v,fn(s,x)=>s+x))'))
    root = Path(__file__).resolve().parents[3]
    modules = [f'--module=zkc::{name}={root}/libraries/zkc/{name}.zkc'
               for name in ['vector', 'finite', 'finite_domain', 'sequence', 'accumulation', 'curve']]
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile',
                             f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                             *modules, 'sample::Packed', f'--output={package}', *flags])
    stored = json.loads(package.read_text())
    deployment = json.loads(stored['artifact'])
    choices = {'simplify': '--no-simplify' not in flags,
               'release_storage': '--release-storage' in flags,
               'fuse_vector_reductions': '--fuse-vector-reductions' in flags,
               'finite_bulk': '--no-finite-bulk' not in flags,
               'calculation_batching': '--no-calculation-batching' not in flags}
    assert stored['options'] == choices
    assert deployment[7] == [str(value).lower() for value in choices.values()]
    bindings = json.loads(deployment[4])[1]
    assert any(binding[1] == 'vector.sum' for binding in bindings) == choices['finite_bulk']
    witness = journal.write('witness.json', {'secret': '7'})
    for rounds in [0, 1, 2]:
        public = journal.write(f'public-{rounds}.json', {'public': '5', 'rounds': str(rounds)})
        args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}',
                f'--public={public}', '--allow-authored']
        proof = directory / f'proof-{rounds}.bin'
        produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                                 f'--witness={witness}', f'--output={proof}'])
        assert not produced['execution']['cleanup_errors']
        expected = b''
        state = 5
        for _ in range(rounds):
            # The root begins once. Child starts use the current state and
            # their own actual shared argument, not the root's public input.
            if empty:
                state = (state * 3 + 5) * 3 + 10
            if nested:
                state = state * 3 + 10
            state = state * 3 + (20 if nested else 10)
            state = state * 3 + 7
            response = 7 + state
            expected += b''.join(v.to_bytes(32, 'big') for v in [7, 7, response, 7])
            state = (state + 1) * 3 + response
        expected += state.to_bytes(32, 'big') * 2
        assert proof.read_bytes() == expected
        verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
        assert verified['status'] == 'accepted'
        assert not verified['execution']['cleanup_errors']


@pytest.mark.parametrize('mutation', ['private-start', 'verifier-private-start', 'omit-start', 'coordinate'])
def test_serialized_child_start_admission(toolchain, journal, directory, mutation):
    source = directory / 'main.zkc'
    source.write_text(composed_source(False))
    package = directory / 'proof.zkpkg'
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', 'sample::Packed', f'--output={package}'])
    deployment = json.loads(json.loads(package.read_text())['artifact'])
    program = json.loads(deployment[4])
    participant = program[3][1 if mutation == 'verifier-private-start' else 0]
    helper = deployment[2][6][6][0][0]
    loop = next(op for op in participant[6] if op[0] == 'loop')
    start = next(op for op in loop[5] if op[0] == 'local' and op[2] == helper)
    if mutation == 'private-start':
        start[3][1] = participant[4][2][0]
        reason = 'native-proof-private-dependency'
    elif mutation == 'verifier-private-start':
        participant[7].append(['private', 'random.bls12-381.fr/0', '2'])
        deployment[6][1][4].append(['4', 'private', 'random.bls12-381.fr/0', '2'])
        loop[5].insert(loop[5].index(start),
                       ['query', 'private_start', 'private', 'draw', [], ['private_value']])
        start[3][1] = 'private_value'
        reason = 'native-proof-private-dependency'
    elif mutation == 'coordinate':
        start[3][-1] = participant[4][1][0]
        reason = 'native-proof-coordinate-operand'
    else:
        # Remove only the invocation, preserving SSA formation and the rest of
        # the state chain. The event schedule must still detect its omission.
        old, new = start[4][0], start[3][0]
        loop[5].remove(start)
        for op in loop[5]:
            if op[0] == 'local':
                op[3] = [new if value == old else value for value in op[3]]
        reason = 'native-proof-state-chain'
    deployment[4] = json.dumps(program)
    reject_deployment(toolchain, journal, directory, deployment, mutation, reason)


@pytest.mark.parametrize('flags', [[], ['--release-storage']])
def test_native_root_can_delegate_to_an_explicit_managed_child(toolchain, journal, directory, flags):
    root = Path(__file__).resolve().parents[3]
    text = (root / 'common/tests/fixtures/constructions/managed.zkc').read_text()
    text += '''
    protocol Outer roles(P,V)(public:F@(P,V),secret:F@P,challenges:Random<F>@V)->(ok:bool@V){
      #[site(step)] let ok=Round roles(P,V)(public,secret,challenges);
      return ok;
    }
    construction Parent for Outer {
      base fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);
      apply Derived at step;
    }
    proof Composed=Outer{prover P;verifier V;public{public};accept ok;construction Parent;}
    '''
    source = directory / 'main.zkc'
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             *library_modules('zkc', overrides={'sample': source}),
                             'sample::Composed', f'--output={package}', *flags])
    public = journal.write('public.json', {'public': '5'})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}']
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                             f'--witness={witness}', f'--output={proof}'])
    assert produced['binding_scope'] == 'transcript'
    verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert verified['status'] == 'accepted'
    assert not verified['execution']['cleanup_errors']


@pytest.mark.parametrize('flags', [[], ['--release-storage']])
def test_child_start_codec_and_conditional_completion(toolchain, journal, directory, flags):
    text = composed_source(False)
    text = text.replace(
        'secret:F@P,challenges:Random<F>@V)->(ok:bool@V){',
        'secret:F@P,challenges:Random<F>@V)->(ok:bool@V) completes{')
    text = text.replace(
        '#[site(final_pick)]',
        'let ()=finish_if @P(done(rounds))();let _=finish_if @V(done(rounds))(ok=true);'
        '#[site(final_pick)]')
    source = directory / 'main.zkc'
    source.write_text(text + '\nfn done(rounds:index)->bool{return rounds==1;}')
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile',
                             f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                             'sample::Packed', f'--output={package}', *flags])
    witness = journal.write('witness.json', {'secret': '7'})
    for rounds, size in [(0, 64), (1, 128), (2, 320)]:
        public = journal.write(f'public-{rounds}.json', {'public': '5', 'rounds': str(rounds)})
        args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}',
                f'--public={public}', '--allow-authored']
        proof = directory / f'proof-{rounds}.bin'
        produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                                 f'--witness={witness}', f'--output={proof}'])
        assert len(proof.read_bytes()) == size
        assert not produced['execution']['cleanup_errors']
        verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
        assert verified['status'] == 'accepted'
        assert not verified['execution']['cleanup_errors']
