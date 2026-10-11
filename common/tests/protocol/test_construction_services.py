"""Selected transcript authority and retained verifier-local randomness."""
import json

import pytest
from test_constructions import SOURCE, reject_deployment
from test_record_codecs import CODEC


@pytest.mark.parametrize('native', [False, True])
@pytest.mark.parametrize('codec', [False, True])
@pytest.mark.parametrize('flags', [[], ['--release-storage']])
def test_retained_verifier_services(toolchain, journal, directory, native, codec, flags):
    text = SOURCE.replace('STATE', '(index,index)').replace('INITIAL', '(0,0)')
    text = text.replace('challenges:Random<T>@V',
                        'before:Random<T>@V,challenges:Random<T>@V,after:Random<T>@V')
    text = text.replace('LOOP_START', 'for _ in 0..rounds roles(P,V) max 2 {').replace('LOOP_END', '}')
    text = text.replace('#[site(challenge)] let c=challenges.draw();', '''
      let a=before.draw();
      let b=after.draw();
      require @V(a+first.0==a+first.1);
      require @V(b+first.0==b+first.1);
      #[site(challenge)] let c=challenges.draw();''')
    construction = ('fiat_shamir("merlin3.bls12-381.fr64be/0",challenges)' if native else
                    'Derived<F,Provider>')
    text = text.replace('construction Derived<F,Provider>;', f'construction {construction};')
    if codec:
        text += CODEC.replace('BASE', f'base {construction};')
    source = directory / 'main.zkc'
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', f'sample::{"Packed" if codec else "Demo"}',
                             f'--output={package}', *flags])
    public = journal.write('public.json', {'public': '5', 'rounds': '2'})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}']
    if not native:
        args.append('--allow-authored')
    proof = directory / 'proof.bin'
    journal.json([toolchain.runtime, '--json', 'prove', *args,
                  f'--witness={witness}', f'--output={proof}'])
    verify = [toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}']
    accepted = journal.json([*verify, '--service=V.before=2', '--service=V.after=2'])
    assert accepted['status'] == 'accepted'
    assert not accepted['execution']['cleanup_errors']
    for service in ['before', 'after']:
        refused = journal.json([*verify, f'--service=V.{service}=1'], refuses='exhausted:resource-budget')
        assert not refused['execution']['cleanup_errors']
    # The replaced authority is not issued as a service, even among retained
    # ports with the same contract on both sides of its original position.
    journal.json([*verify, '--service=V.challenges=1'], refuses='entry-service-names')
    public.write_text(json.dumps({'public': '5', 'rounds': '0'}))
    journal.json([toolchain.runtime, '--json', 'prove', *args,
                  f'--witness={witness}', f'--output={proof}'])
    assert journal.json([*verify, '--service=V.before=0', '--service=V.after=0'])['status'] == 'accepted'


def test_private_verifier_entropy_cannot_replace_a_delivery(toolchain, journal, directory):
    text = SOURCE.replace('STATE', '()').replace('INITIAL', '()')
    text = text.replace('LOOP_START', '').replace('LOOP_END', '')
    text = text.replace('challenges:Random<T>@V', 'challenges:Random<T>@V,private:Random<T>@V')
    text = text.replace('let c=challenges.draw();', 'let c=private.draw();')
    text = text.replace('construction Derived<F,Provider>;',
                        'construction fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);')
    # Remove an unused construction whose exact coverage intentionally no
    # longer matches this altered protocol.
    start = text.index('construction Derived<')
    end = text.index('component Provider:', start)
    text = text[:start] + text[end:]
    source = directory / 'main.zkc'
    source.write_text(text)
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', 'sample::Demo', f'--output={directory / "proof.zkpkg"}'],
                 refuses='native-proof-reverse-message')


@pytest.mark.parametrize('codec', [False, True])
@pytest.mark.parametrize('mutation', ['state', 'count', 'old-root'])
def test_private_reply_admission_on_serialized_program(toolchain, journal, directory, codec, mutation):
    # Alter an otherwise valid serialized program to exercise independent
    # admission of private replies into shared state and control.
    text = SOURCE.replace('STATE', '(index,index)').replace('INITIAL', '(0,0)')
    text = text.replace('LOOP_START', 'for _ in 0..rounds roles(P,V) max 2 {' if mutation == 'count' else '')
    text = text.replace('LOOP_END', '}' if mutation == 'count' else '')
    if codec:
        text += CODEC.replace('BASE', 'base Derived<F,Provider>;')
    source = directory / 'main.zkc'
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', f'sample::{"Packed" if codec else "Demo"}',
                  f'--output={package}'])
    original = json.loads(json.loads(package.read_text())['artifact'])
    program = json.loads(original[4])
    verifier = program[3][1]
    verifier[7].append(['private', 'random.bls12-381.fr/0', '2'])
    original[6][1][4].append(['4', 'private', 'random.bls12-381.fr/0', '2'])
    # Convert a private reply into an index, then substitute it for a copyable
    # state slot of the query adapter. The byte-codec path has completed its
    # preceding receive group here, so the dependency pass sees the mutation.
    functions = {f[1]: f for f in program[2]}
    adapters = {a[0] for a in original[2][6][6] if a[1] == 'local'}
    target = (next(op for op in verifier[6] if op[0] == 'loop') if mutation == 'count' else
              next(op for op in verifier[6] if op[0] == 'local' and op[2] in adapters
                   and functions[op[2]][3][0] == 'field:bls12-381.fr@arkworks.fr/0'))
    eq = next(b[0] for b in program[1] if b[1] == 'field.equal')
    constant = next(b[0] for b in program[1] if b[1] == 'index.constant')
    program[2].append(['function', 'private_index', [['value', 'field:bls12-381.fr@arkworks.fr/0']],
                       ['index@native.index/0'], [
                           ['op', 'equal', eq, [], ['value', 'value'], ['condition']],
                           ['op', 'zero', constant, ['0'], [], ['zero']],
                           ['if', 'branch', 'condition', ['zero'],
                            [['yield', ['zero']]], [['yield', ['zero']]], ['result']],
                           ['return', ['result']]], ['private_index', []]])
    index = verifier[6].index(target)
    verifier[6][index:index] = [
        ['query', 'private-draw', 'private', 'draw', [], ['private_value']],
        ['local', 'private-convert', 'private_index', ['private_value'], ['private_count']]]
    if mutation == 'count':
        target[2][1] = 'private_count'
    elif mutation == 'old-root':
        # The obsolete state remains copyable ordinary data. Reading it cannot
        # panic in dependency admission, but it cannot replace the live state.
        target[3][0] = verifier[6][0][4][0]
    else:
        target[3][0] = 'private_count'
    original[4] = json.dumps(program)
    reject_deployment(toolchain, journal, directory, original, mutation,
                      'native-proof-state-chain' if mutation == 'old-root' else
                      'native-proof-private-dependency')


MIXED = '''module sample;
domain F=field("bls12-381.fr");
domain E=field("koala-bear.ext8-binomial3");
domain Host=transcript("merlin3.bls12-381.fr64be/0");
interface ProviderType {type State:Copy+Drop;fn initialize()->State;}
component Provider:ProviderType {
  type State:Copy+Drop=index;
  fn initialize()->State{return State(0);}
}
protocol Choose roles(P,V)(
  first:Random<F>@V, before:Random<F>@V, second:Random<F>@V,
  extension:Random<E>@V, after:Random<E>@V)->(ok:bool@V){
  let private=before.draw();
  require @V(private==private);
  #[site(base)] let a=first.draw();
  #[site(base_delivery)] let ap=send V->P(a);
  #[site(other)] let b=second.draw();
  #[site(other_delivery)] let bp=send V->P(b);
  #[site(extended)] let e=extension.draw();
  #[site(extension_delivery)] let ep=send V->P(e);
  #[site(pick_index)] let i=extension.index<3>();
  #[site(index_delivery)] let ip=send V->P(i);
  #[site(response)] let result=send P->V((ap,bp,ep,ip));
  let private2=after.draw();
  require @V(private2==private2);
  require @V(result.0==a);require @V(result.1==b);
  require @V(result.2==e);require @V(result.3==i);
  return true;
}
construction Mixed for Choose {
  transcript PROVIDER;
  replace {extension,first,second};
  on start(t){return t;}
  on query base(t){return (t,2);}
  on query other(t){return (t,3);}
  on query extended(t){return (t,4);}
  on query pick_index(t,bound){return (t,bound-1);}
  on message {base_delivery,other_delivery,extension_delivery,index_delivery,response}(t,value){return t;}
}
protocol Outer roles(A,B)(rounds:index@(A,B),
  first:Random<F>@B, before:Random<F>@B, second:Random<F>@B,
  extension:Random<E>@B, after:Random<E>@B)->(ok:bool@B){
  let mut accepted@B=true;
  for _ in 0..rounds roles(A,B) max 2 {
    #[site(child)] let result=Choose roles(A,B)(first,before,second,extension,after);
    accepted=result;
  }
  return accepted;
}
construction Parent for Outer {
  transcript PROVIDER;replace {first,second,extension};
  on start(t){return t;}
  apply Mixed at child;
}
proof Demo=Outer{prover A;verifier B;public{rounds};accept ok;construction Parent;}
'''


@pytest.mark.parametrize('managed', [False, True])
@pytest.mark.parametrize('alias', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_mixed_authorities_across_repeated_calls(toolchain, journal, directory, managed, alias, flags):
    provider = ('Host' if managed else 'Provider')
    text = MIXED.replace('PROVIDER', provider)
    if alias:
        text = text.replace('(first,before,second,extension,after)', '(first,before,first,extension,after)')
        # Both child ports are selected even when they alias one parent authority.
        text = text.replace('transcript ' + provider + ';replace {first,second,extension};',
                            'transcript ' + provider + ';replace {first,extension};')
    source = directory / 'main.zkc'
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Demo', f'--output={package}', *flags])
    envelope = json.loads(package.read_text())
    deployment = json.loads(envelope['artifact'])
    assert deployment[2][1][6] == (['1', '4'] if alias else ['1', '3', '4'])
    proof = directory / 'proof.bin'
    for rounds in [0, 2]:
        public = journal.write(f'public-{rounds}.json', {'rounds': str(rounds)})
        args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}',
                f'--public={public}', '--allow-authored']
        journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'])
        verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}',
                                 f'--service=B.before={rounds}', f'--service=B.after={rounds}'])
        assert verified['status'] == 'accepted'
        assert not verified['execution']['cleanup_errors']
        observations = [r for r in verified['execution']['resources'] if r['kind'] == 'service']
        assert sorted(r['state']['transitions'] for r in observations) == (
            [0, rounds, rounds] if alias else [rounds, rounds])
    # The policy's source coordinates cannot be duplicated, reordered, or changed
    # into a retained service. Admission checks the independently emitted maps.
    for replaced, reason in [(['1', '1'], 'native-proof-policy'),
                             (['4', '1'], 'native-proof-policy'),
                             (['0', '1', '4'], 'native-proof-service-map'),
                             (['1', '2', '4'], 'native-proof-service-map')]:
        changed = json.loads(json.dumps(deployment))
        changed[2][1][6] = replaced
        reject_deployment(toolchain, journal, directory, changed, 'authority-map', reason)


@pytest.mark.parametrize('old,new', [
    ('replace {extension,first,second};', 'replace {first,first,extension};'),
    ('replace {extension,first,second};', 'replace {};'),
    ('replace {first,second,extension};', 'replace {first,extension};'),
    ('replace {first,second,extension};', 'replace {first,before,second,extension};'),
    ('before:Random<F>@V', 'before:Random<F>@P'),
    ('Choose roles(A,B)(first,before,second,extension,after)',
     'Choose roles(A,B)(first,first,second,extension,after)'),
])
def test_authority_set_refusals(toolchain, journal, directory, old, new):
    text = MIXED.replace('PROVIDER', 'Provider').replace(old, new)
    if old == 'before:Random<F>@V':
        text = text[:text.index('protocol Outer')]
        text = text.replace('require @V(private==private);', 'require @P(private==private);')
        text = text.replace('replace {extension,first,second};', 'replace {extension,first,before,second};')
        text += 'proof Demo=Choose{prover P;verifier V;public{};accept ok;construction Mixed;}'
    source = directory / 'main.zkc'
    source.write_text(text)
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', 'sample::Demo', f'--output={directory / "proof.zkpkg"}'],
                 refuses='source.name' if new == 'replace {};' else 'source.construction')


@pytest.mark.parametrize('native', [False, True])
def test_private_prover_count_without_child_start(toolchain, journal, directory, native):
    text = SOURCE.replace('STATE', '(index,index)').replace('INITIAL', '(0,0)')
    text = text.replace('LOOP_START', 'for _ in 0..rounds roles(P,V) max 2 {').replace('LOOP_END', '}')
    if native:
        text = text.replace('construction Derived<F,Provider>;',
                            'construction fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);')
    source = directory / 'main.zkc'
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', 'sample::Demo', f'--output={package}'])
    deployment = json.loads(json.loads(package.read_text())['artifact'])
    program = json.loads(deployment[4])
    producer = program[3][0]
    eq = next(b[0] for b in program[1] if b[1] == 'field.equal')
    program[2].append(['function', 'witness_count',
                      [['secret', 'field:bls12-381.fr@arkworks.fr/0'], ['count', 'index@native.index/0']],
                       ['index@native.index/0'], [
                           ['op', 'equal', eq, [], ['secret', 'secret'], ['condition']],
                           ['if', 'branch', 'condition', ['count'],
                            [['yield', ['count']]], [['yield', ['count']]], ['result']],
                           ['return', ['result']]], ['witness_count', []]])
    loop = next(op for op in producer[6] if op[0] == 'loop')
    position = producer[6].index(loop)
    producer[6].insert(position, ['local', 'private_count', 'witness_count',
                                [producer[4][2][0], loop[2][1]], ['private_count']])
    loop[2][1] = 'private_count'
    deployment[4] = json.dumps(program)
    reject_deployment(toolchain, journal, directory, deployment, 'private-count',
                      'native-proof-private-dependency')


@pytest.mark.parametrize('native', [False, True])
@pytest.mark.parametrize('codec', [False, True])
def test_private_query_cannot_split_selected_delivery(toolchain, journal, directory, native, codec):
    text = SOURCE.replace('STATE', '()').replace('INITIAL', '()')
    text = text.replace('LOOP_START', '').replace('LOOP_END', '')
    text = text.replace('challenges:Random<T>@V', 'challenges:Random<T>@V,private:Random<T>@V')
    text = text.replace('let c=challenges.draw();', 'let c=challenges.draw();let p=private.draw();')
    base = ('fiat_shamir("merlin3.bls12-381.fr64be/0",challenges)' if native else
            'Derived<F,Provider>')
    text = text.replace('construction Derived<F,Provider>;', f'construction {base};')
    if codec:
        text += CODEC.replace('BASE', f'base {base};')
    source = directory / 'main.zkc'
    source.write_text(text)
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', f'sample::{"Packed" if codec else "Demo"}',
                  f'--output={directory / "proof.zkpkg"}'],
                 refuses='native-proof-prefix')
