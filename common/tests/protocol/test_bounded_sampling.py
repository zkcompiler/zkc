"""Library rejection sampling, explicit exhaustion and unchanged snapshots."""
import json
from pathlib import Path

import pytest
from input_files import input_files

SOURCE = '''module sample;
use zkc::sampling::{Words,uniform_index};
module TestWords:Words {
  type State:Copy+Drop=(index,index);
  pub fn start(word:index,count:index)->State{return State((word,count));}
  pub fn draw_count(state:State)->index{let(_,count)=unpack(state);return count;}
  fn next(state:State)->(State,index){
    let(word,count)=unpack(state);
    let value=if count==0 {word} else {18446744073709551615};
    return (State((word,count+1)),value);
  }
}
fn sample(first:index,bound:index)->(index,index){
  let(state,value)=uniform_index<TestWords,ATTEMPTS>(TestWords::start(first,0),bound);
  return(value,TestWords::draw_count(state));
}
protocol Sample roles(P)(first:index@P,bound:index@P)->(value:index@P,count:index@P){
  let(value,count)=sample(first,bound);
  return(value=value,count=count);
}
run Demo=Sample;
'''


@pytest.mark.parametrize('attempts', [0, 1, 2])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_bounded_word_sampling(toolchain, journal, directory, attempts, flags):
    source = directory / 'main.zkc'
    source.write_text(SOURCE.replace('ATTEMPTS', str(attempts)))
    library = Path(__file__).resolve().parents[3] / 'libraries/zkc/sampling.zkc'
    package = directory / 'sampling.zkpkg'
    built = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                          f'--module=sample={source}', f'--module=zkc::sampling={library}',
                          'sample::Demo', f'--output={package}', *flags])
    maximum = (1 << 64) - 1
    # Exercise both sides of the exact threshold, powers of two, the singleton
    # range and bounds above 2^63 without overflowing the threshold formula.
    for bound in [0, 1, 2, 3, 10, (1 << 63) + 1, maximum]:
        threshold = (1 << 64) % bound if bound else 0
        for first in sorted({0, maximum, threshold, max(0, threshold - 1)}):
            candidates = [first, maximum][:attempts]
            accepted = next(((i + 1, value % bound) for i, value in enumerate(candidates)
                             if bound and value >= threshold), None)
            name = f'{bound}-{first}'
            inputs = input_files(journal, name + '.json', session='sampling',
                                 roles={'P': {'inputs': {'first': str(first), 'bound': str(bound)}}})
            output = directory / (name + '.results.json')
            report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                                   f'--sha256={built["package_sha256"]}', *inputs, f'--results={output}'],
                                  refuses=None if accepted else 'entry-run-incomplete')
            if accepted:
                count, value = accepted
                assert json.loads(output.read_text())['roles']['P'] == {
                    'value': str(value), 'count': str(count)}
            else:
                after = report['execution']['roles'][0]['after']
                assert after[0] == 'stopped'
                assert after[1]['cause'][0] == 'explicit'
                assert after[1]['cause'][1]['text'] == ('exhausted' if bound else 'reject')


@pytest.mark.parametrize('bound', [3, 10, 18446744073709551615])
def test_non_power_of_two_construction_uses_an_explicit_sampler(toolchain, journal, directory, bound):
    text = SOURCE[:SOURCE.index('fn sample')]
    text += '''
    domain E=field("koala-bear.ext8-binomial3");
    interface ProviderType {type State:Copy+Drop;fn initialize()->State effects();}
    module Provider:ProviderType {
      type State:Copy+Drop=index;
      pub fn wrap(value:index)->State{return State(value);}
      pub fn raw(state:State)->index{return unpack(state);}
      fn initialize()->State{return State(0);}
    }
    protocol Choose roles(P,V)(expected:index@(P,V),coins:Random<E>@V)->(ok:bool@V){
      #[site(pick)] let value=coins.index<BOUND>();
      #[site(delivery)] let actual=send V->P(value);
      #[site(response)] let received=send P->V(actual);
      return received==expected;
    }
    construction Custom for Choose {
      transcript Provider;replace coins;
      on start(t){return t;}
      on query pick(t,bound){
        let(next,value)=uniform_index<TestWords,2>(TestWords::start(0,Provider::raw(t)),bound);
        let count=TestWords::draw_count(next);
        return(Provider::wrap(count),value);
      }
      on message {delivery,response}(t,value){return t;}
    }
    proof Demo=Choose{prover P;verifier V;public{expected};accept ok;construction Custom;}
    proof Native=Choose{prover P;verifier V;public{expected};accept ok;
      construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0",coins);}
    '''
    source = directory / 'main.zkc'
    source.write_text(text.replace('BOUND', str(bound)))
    library = Path(__file__).resolve().parents[3] / 'libraries/zkc/sampling.zkc'
    modules = [f'--module=sample={source}', f'--module=zkc::sampling={library}']
    package = directory / 'sampling.zkpkg'
    built = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                          *modules, 'sample::Demo', f'--output={package}'])
    public = journal.write('public.json', {'expected': str(((1 << 64) - 1) % bound)})
    proof = directory / 'proof.bin'
    args = [f'--package={package}', f'--sha256={built["package_sha256"]}',
            f'--public={public}', '--allow-authored']
    journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'])
    assert journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])['status'] == 'accepted'
    # The default native suite still owns its existing power-of-two byte map.
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  *modules, 'sample::Native', f'--output={directory / "native.zkpkg"}'],
                 refuses='native-proof-index-bound')


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_explicit_transcript_trials_preserve_state_and_charge_work(toolchain, journal, directory, flags):
    # The installed OpenVM transition checks the live data state. A library
    # author makes a trial by passing a copy and retaining the original state.
    text = '''module sample;
    type Indices=builtin("indices");
    domain E=field("koala-bear.ext8-binomial3");
    interface ProviderType {type State:Copy+Drop;fn initialize()->State effects(stop);}
    module Provider:ProviderType {
      type State:Copy+Drop=Indices;
      pub fn wrap(value:Indices)->State{return State(value);}
      pub fn raw(state:State)->Indices{return unpack(state);}
      fn initialize()->State{return State(kernel("external.openvm.init"));}
    }
    protocol Choose roles(P,V)(coins:Random<E>@V)->(ok:bool@V){
      #[site(pick)] let value=coins.index<16>();
      #[site(delivery)] let actual=send V->P(value);
      #[site(response)] let received=send P->V(actual);
      return received==value;
    }
    construction Custom for Choose {
      transcript Provider;replace coins;
      on start(t){
        let original=Provider::raw(t);
        TRIALS
        return t;
      }
      on query pick(t,bound){
        let(next,value)=kernel("external.openvm.sample_bits",Provider::raw(t),4);
        return(Provider::wrap(next),value);
      }
      on message {delivery,response}(t,value){return t;}
    }
    proof Demo=Choose{prover P;verifier V;public{};accept ok;construction Custom;}
    '''
    trials = '''
      let(zero,accepted)=kernel("external.openvm.check_witness",original,0,5);
      require accepted;
      let(failed,ok)=kernel("external.openvm.check_witness",original,30,5);
      require kernel("bool.not",ok);
      let(failed_again,ok_again)=kernel("external.openvm.check_witness",original,30,5);
      require kernel("bool.not",ok_again);
      let(_,before)=kernel("external.openvm.sample",original);
      let(_,after_zero)=kernel("external.openvm.sample",zero);
      let(_,after_failed)=kernel("external.openvm.sample",failed);
      let(_,after_again)=kernel("external.openvm.sample",failed_again);
      require before==after_zero;
      require after_failed==after_again;
      require kernel("bool.not",before==after_failed);
    '''
    proofs, costs = [], []
    for trial in [False, True]:
        source = directory / 'main.zkc'
        source.write_text(text.replace('TRIALS', trials if trial else ''))
        package = directory / f'{trial}.zkpkg'
        built = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                              f'--module=sample={source}', 'sample::Demo', f'--output={package}', *flags])
        proof = directory / f'{trial}.bin'
        args = [f'--package={package}', f'--sha256={built["package_sha256"]}', '--allow-authored']
        produced = journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'])
        verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
        assert produced['execution']['external_work'] == verified['execution']['external_work']
        costs.append(produced['execution']['external_work'])
        # Native headers bind distinct source constructions. The mathematical
        # response is the same after the discarded trials.
        proofs.append(proof.read_bytes()[-8:])
        if trial:
            limited = directory / 'limited.bin'
            stopped = journal.json([toolchain.runtime, '--json', 'prove', *args,
                                    f'--output={limited}', f'--external-work={costs[0]}'],
                                   refuses='exhausted:external-work-limit')
            assert not limited.exists()
            assert not stopped['execution']['cleanup_errors']
    assert proofs[0] == proofs[1]
    # Two failed checks cost 3 each; two samples from the empty snapshot cost
    # 2 each, and two samples from the checked snapshot cost 1 each.
    assert costs[1] - costs[0] == 12
