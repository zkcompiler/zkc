"""Selected source -> package -> Rust proof Host acceptance and contrary inputs.

These intentionally disclose the witness. Arithmetic, state/record threading,
origin correspondence and complete outcomes are tested, not cryptographic laws.
No generated MLIR or hand-authored executable can replace the source producer.
"""
import json
import re
from pathlib import Path

import pytest

FIXTURES = Path(__file__).resolve().parents[1] / 'fixtures/selected-native-proofs'
MERLIN = 'merlin3.bls12-381.fr64be/0'
KECCAK = 'hash-chain.keccak256.bls12-381.fr64be/0'
PRODUCER, VALIDATOR = 'role00000000', 'role00000001'
PUBLIC_TYPES = ['bool', 'index', 'field:bls12-381.fr', 'bool', 'bool']


def source_text(name='square'):
    return (FIXTURES / f'{name}.zkc').read_text()


def between(text, name):
    return text.split(f'// {name}_BEGIN\n', 1)[1].split(f'// {name}_END', 1)[0]


def origin_tree(encoded):
    """Read the retained logical-tree framing, including every origin frame."""
    data = bytes.fromhex(encoded)

    def read(at):
        assert at + 9 <= len(data)
        tag, size = data[at], int.from_bytes(data[at + 1:at + 9], 'little')
        at += 9
        if tag == 0:
            assert at + size <= len(data)
            return data[at:at + size].decode(), at + size
        assert tag == 1
        children = []
        for _ in range(size):
            child, at = read(at)
            children.append(child)
        return children, at

    value, end = read(0)
    assert end == len(data)
    assert len(value) == 5 and value[0] == 'zkc.native-origin-template/0'
    assert value[3] == []
    return value


def native_label(name):
    return 'label_' + name.encode().hex()


def native_paths(paths):
    """Expected original occurrence paths from the authored labels and tuple shapes."""
    result = {}
    for name, path in paths.items():
        scope = None
        frames = []
        for kind, label, *alternative in path:
            site = native_label(label)
            if scope is not None:
                branch, arm = scope
                site = f'branch_{len(branch)}_{branch}_arm_{len(arm)}_{arm}_{site}'
            frames.append((kind, site, *alternative))
            if kind == 'branch':
                scope = site, alternative[0]
        site = native_label(name)
        if scope is not None:
            branch, arm = scope
            site = f'branch_{len(branch)}_{branch}_arm_{len(arm)}_{arm}_{site}'
        if name.startswith('challenge'):
            leaves = [site]
        elif name.startswith(('commitment', 'response', 'tally')):
            leaves = [site + '_0', site + '_1']
        else:
            leaves = [site + '_0']
        result.update((leaf, tuple(frames)) for leaf in leaves)
    return result


def compile_source(toolchain, journal, directory, text, paths, *, codec=False, flags=(), suite=MERLIN):
    source = directory / 'main.zkc'
    source.write_text(text)
    package = directory / 'proof.zkpkg'
    compiled = journal.json([
        toolchain.runtime, '--json', 'compile', '--source-format=zkc',
        f'--compiler={toolchain.compiler}', f'--module=selected={source}',
        'selected::Demo', f'--output={package}', *flags,
    ])
    assert compiled['status'] == 'compiled'
    deployment = json.loads(json.loads(package.read_text())['artifact'])
    descriptor = deployment[2]
    policy = descriptor[1]
    assert policy[2:5] == [PRODUCER, VALIDATOR, '0']
    assert policy[6:8] == [['6'], ['0', '1', '2', '3', '4']]
    assert policy[5] == ('' if codec else suite)
    assert policy[9] == ('raw.bytes/0' if codec else 'zkc.framed/0')
    assert [row[:3] for row in descriptor[4]] == [
        [VALIDATOR, str(i), kind] for i, kind in enumerate(PUBLIC_TYPES)
    ]

    # Preserve the complete original map, including unused public formals and
    # the private witness, then compare it with the actual Runner signatures.
    participants = {p[1]: p for p in json.loads(deployment[4])[3]}
    assert {row[0] for row in deployment[6]} == {PRODUCER, VALIDATOR}
    for role, participant, inputs, outputs, services, acceptance in deployment[6]:
        kinds = PUBLIC_TYPES + (['field:bls12-381.fr'] if role == PRODUCER else [])
        assert inputs == [[str(i), kind] for i, kind in enumerate(kinds)]
        assert outputs == ([] if role == PRODUCER else [['0', 'bool']])
        assert services == [] and acceptance == ('' if role == PRODUCER else '0')
        actual = participants[participant]
        assert actual[3] == role
        hidden_inputs = int(role == VALIDATOR) if codec else 1
        assert len(actual[4]) == len(inputs) + hidden_inputs
        assert [port[1].split('@', 1)[0] for port in actual[4][:len(inputs)]] == kinds
        assert len(actual[5]) == len(outputs) + 1 + int(codec and role == PRODUCER)

    # Compare the whole static event inventory, not only the executed arm.
    observed = {}
    for event in descriptor[3]:
        origin = origin_tree(event[1])
        assert origin[1] == policy[1]
        assert origin[4][0] in ('message', 'query')
        assert origin[4][1] == policy[1]
        site = origin[4][2]
        assert site not in observed
        assert all(frame[1] == policy[1] for frame in origin[2])
        observed[site] = tuple((frame[0], *frame[2:]) for frame in origin[2])
        if origin[4][0] == 'query':
            assert origin[4][3:] == ['input_6', 'random.bls12-381.fr/0', 'draw', VALIDATOR]
        if any(site.endswith(native_label(name) + '_0')
               for name in ('request', 'joined_request')):
            assert event[0] == 'reconstructed-message'
            assert origin[4][-2:] == [VALIDATOR, PRODUCER]
    assert observed == native_paths(paths)
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}']
    if codec:
        args.append('--allow-authored')
    return args


def public_values(choice=True, rounds=1, enabled=True, finish=False):
    return {'choice': choice, 'rounds': str(rounds), 'public': '49',
            'enabled': enabled, 'finish': finish}


def clean(result):
    assert not result['execution']['cleanup_errors']


def prove(toolchain, journal, directory, args, public, name='honest', refuses=None):
    public_file = journal.write(f'{name}-public.json', public)
    witness = journal.write(f'{name}-witness.json', {'secret': '7'})
    proof = directory / f'{name}.bin'
    invocation = [*args, f'--public={public_file}']
    result = journal.json([
        toolchain.runtime, '--json', 'prove', *invocation,
        f'--witness={witness}', f'--output={proof}',
    ], refuses=refuses)
    clean(result)
    if refuses is None:
        assert result['status'] == 'produced'
        assert proof.exists()
    else:
        assert not proof.exists()
        assert result['execution']['stop']['role'] == PRODUCER
        assert result['execution']['stop']['kind'] == 'Explicit("reject")'
    return proof, invocation, result


def verify(toolchain, journal, args, proof, refuses=None):
    result = journal.json([
        toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}',
    ], refuses=refuses)
    clean(result)
    if refuses is None:
        assert result['status'] == 'accepted'
        assert result['execution']['verification_decision'] == 'accepted'
    return result


def proof_frames(proof):
    data = proof.read_bytes()
    assert data[:8] == b'ZKCPRF00'
    at, frames = 40, []
    while at < len(data):
        assert at + 8 <= len(data)
        size = int.from_bytes(data[at:at + 8], 'little')
        at += 8
        assert size and at + size <= len(data)
        frames.append(data[at:at + size])
        at += size
    assert at == len(data)
    return frames


def round_paths(path, suffix=''):
    return {site + suffix: path for site in ('commitment', 'challenge', 'delivery', 'response')}


CHOSEN = (('branch', 'choose', 'then'),)


def exercise_native(toolchain, journal, directory, text, paths, public, rounds, *, flags=(),
                    extra_transitions=0, suite=MERLIN):
    args = compile_source(toolchain, journal, directory, text, paths, flags=flags, suite=suite)
    proof, invocation, produced = prove(toolchain, journal, directory, args, public)
    accepted = verify(toolchain, journal, invocation, proof)
    assert produced['binding_scope'] == accepted['binding_scope'] == 'transcript'
    assert len(proof_frames(proof)) == 4 * rounds + 2
    for result in (produced, accepted):
        transcript = [r for r in result['execution']['resources'] if r['kind'] == 'capability' and r['stage'] == 'transcript']
        assert len(transcript) == 1
        # Each round observes four payload leaves and one delivery, then draws.
        # The final tally contributes two observations; initialization is not a transition.
        assert transcript[0]['transitions'] == 6 * rounds + 2 + extra_transitions

    # A full public change must fail even for the zero-trip/event-free route.
    changed_public = journal.write('changed-public.json', {**public, 'public': '64'})
    verify(toolchain, journal, [*args, f'--public={changed_public}'], proof, 'proof-header')
    changed_selector = journal.write('changed-selector.json',
                                     {**public, 'choice': not public['choice']})
    verify(toolchain, journal, [*args, f'--public={changed_selector}'], proof, 'proof-header')
    # Keep framing and canonical field encoding; falsify the second tally.
    changed = directory / 'changed-tally.bin'
    changed.write_bytes(proof.read_bytes()[:-32] + bytes(31) + b'\x01')
    verify(toolchain, journal, invocation, changed, 'artifact-rejected')
    return args


@pytest.mark.parametrize('choice,flags', [
    pytest.param(True, (), id='chosen'),
    pytest.param(False, (), id='dormant'),
    pytest.param(True, ('--no-simplify',), id='chosen-no-simplify'),
    pytest.param(False, ('--no-simplify',), id='dormant-no-simplify'),
])
def test_merlin_selected_and_event_free_arm(toolchain, journal, directory, choice, flags):
    # A false guard in the dormant arm must remain unreached.
    public = public_values(choice=choice, enabled=choice)
    args = exercise_native(toolchain, journal, directory, source_text(),
                           {**round_paths(CHOSEN), 'tally': ()}, public, int(choice), flags=flags)
    if choice:
        prove(toolchain, journal, directory, args, {**public, 'enabled': False},
              'source-stop', 'artifact-stopped')


@pytest.mark.parametrize('nesting,rounds,suite', [
    pytest.param(nesting, rounds, suite, id=f'{nesting}-{rounds}{suffix}')
    for suite, suffix in [(MERLIN, ''), (KECCAK, '-keccak')]
    for nesting in ('branch-in-repeat', 'repeat-in-branch')
    for rounds in (0, 1, 3)
])
def test_selected_repeat_occurrences(toolchain, journal, directory, nesting, rounds, suite):
    text = source_text().replace(MERLIN, suite)
    region = 'SELECTED' if nesting == 'branch-in-repeat' else 'ROUND'
    body = between(text, region)
    text = text.replace(body, '#[site(iterations)] for _ in 0..rounds roles(P,V) max 3 {\n'
                        + body + '\n}\n', 1)
    loop = (('repeat', 'iterations'),)
    path = loop + CHOSEN if nesting == 'branch-in-repeat' else CHOSEN + loop
    exercise_native(toolchain, journal, directory, text,
                    {**round_paths(path), 'tally': ()}, public_values(rounds=rounds), rounds, suite=suite)


@pytest.mark.parametrize('choice', [True, False], ids=['one-round', 'two-rounds'])
def test_unequal_arm_counts(toolchain, journal, directory, choice):
    text = source_text()
    body = between(text, 'ROUND')

    def renamed(suffix):
        return re.sub(r'\b(commitment|challenge|delivery|response|first|actual|last|'
                      r'prover_guard|verifier_guard)\b',
                      lambda match: match[0] + suffix, body)

    text = text.replace('// DORMANT', renamed('Other') + renamed('Extra'))
    other = (('branch', 'choose', 'else'),)
    paths = {**round_paths(CHOSEN), **round_paths(other, 'Other'),
             **round_paths(other, 'Extra'), 'tally': ()}
    exercise_native(toolchain, journal, directory, text, paths,
                    public_values(choice=choice), 1 if choice else 2)


@pytest.mark.parametrize('choice', [True, False], ids=['request-arm', 'request-dormant'])
def test_reverse_request_and_joined_replica(toolchain, journal, directory, choice):
    text = source_text().replace('// SELECTED_BEGIN', '''
      let mut requested@V=public;
      let mut requested_copy@P=public;
      // SELECTED_BEGIN''').replace('// ROUND_BEGIN', '''
      requested=requested+public;
      requested_copy=requested_copy+public;
      #[site(request)] let request=send V->P(requested);
      require @P(request==requested_copy);
      // ROUND_BEGIN''').replace('// SELECTED_END', '''
      // SELECTED_END
      #[site(joined_request)] let joined=send V->P(requested);
      require @P(joined==requested_copy);''')
    paths = {**round_paths(CHOSEN), 'request': CHOSEN, 'joined_request': (), 'tally': ()}
    exercise_native(toolchain, journal, directory, text, paths,
                    public_values(choice=choice), int(choice), extra_transitions=1 + int(choice))


@pytest.mark.parametrize('scenario', ['continue', 'complete', 'dormant', 'stop'])
def test_selected_codec_outcomes(toolchain, journal, directory, scenario):
    # This fixture keeps messages outside the selection and completion inside.
    # The separate arm-local case checks custom selector association as well.
    args = compile_source(toolchain, journal, directory, source_text('codec'),
                          round_paths(()), codec=True, flags=('--release-storage',))
    public = public_values(choice=scenario != 'dormant', finish=scenario in ('complete', 'dormant'),
                           enabled=scenario != 'dormant')
    proof, invocation, produced = prove(toolchain, journal, directory, args, public)
    # Independent arithmetic oracle: start=49, observe(7)=154, draw=154.
    values = [7, 7]
    if scenario != 'complete':
        values += [(98 if public['choice'] else 49) + 154, 7]
    assert proof.read_bytes() == b''.join(value.to_bytes(32, 'big') for value in values)
    accepted = verify(toolchain, journal, invocation, proof)
    for result in (produced, accepted):
        assert (result['execution']['return_at'] is not None) == (scenario == 'complete')

    changed_public = journal.write('changed-public.json', {**public, 'public': '50'})
    verify(toolchain, journal, [*args, f'--public={changed_public}'], proof, 'artifact-rejected')
    changed = directory / 'changed-payload.bin'
    changed.write_bytes(proof.read_bytes()[:-32] + bytes(32))
    verify(toolchain, journal, invocation, changed, 'artifact-rejected')
    trailing = directory / 'trailing.bin'
    trailing.write_bytes(proof.read_bytes() + b'\xff')
    # Both ordinary and conditional successful completion run Packing.finish.
    verify(toolchain, journal, invocation, trailing, 'artifact-stopped')

    if scenario == 'stop':
        stopped = {**public, 'enabled': False}
        prove(toolchain, journal, directory, args, stopped, 'source-stop', 'artifact-stopped')
        stopped_public = journal.write('stopped-public.json', stopped)
        stop_args = [*args, f'--public={stopped_public}']
        original_stop = verify(toolchain, journal, stop_args, proof, 'artifact-stopped')
        malformed = directory / 'unreached-response.bin'
        malformed.write_bytes(proof.read_bytes()[:64] + b'\xff')
        malformed_stop = verify(toolchain, journal, stop_args, malformed, 'artifact-stopped')
        for result in (original_stop, malformed_stop):
            assert result['execution']['stop']['role'] == VALIDATOR
            assert result['execution']['stop']['kind'] == 'Explicit("reject")'
            assert result['execution']['return_at'] is None
        # Local authored callbacks consume instructions, not external service work.
        assert original_stop['execution']['instructions'] < accepted['execution']['instructions']
        assert original_stop['execution']['instructions'] == malformed_stop['execution']['instructions']


@pytest.mark.parametrize('scenario', ['continue', 'complete', 'dormant', 'stop'])
def test_arm_local_custom_codec_outcomes(toolchain, journal, directory, scenario):
    text = source_text('codec')
    begin = text.index('  #[site(commitment)]')
    end = text.index('\nconstruction Derived')
    text = text[:begin] + """
  let mut accepted@V=true;
  #[site(choose)] if choice roles(P,V) {
    #[site(commitment)] let first=send P->V((secret,secret));
    #[site(challenge)] let challenge=challenges.draw();
    #[site(delivery)] let actual=send V->P(challenge);
    accepted=first.0*first.1==public;
    require @P(enabled);
    require @V(enabled);
    let ()=finish_if @P(finish)();
    let _=finish_if @V(finish)(ok=accepted);
    #[site(response)] let last=send P->V((secret*secret+public+actual,secret));
    accepted=accepted && last.0==public+public+challenge && last.1==first.1;
  } else {}
  return accepted;
}
""" + text[end:]
    args = compile_source(toolchain, journal, directory, text,
                          round_paths(CHOSEN), codec=True, flags=('--release-storage',))
    public = public_values(choice=scenario != 'dormant',
                           finish=scenario in ('complete', 'dormant'))
    proof, invocation, produced = prove(toolchain, journal, directory, args, public)
    values = [] if scenario == 'dormant' else [7, 7]
    if scenario not in ('complete', 'dormant'):
        values += [252, 7]
    assert proof.read_bytes() == b''.join(value.to_bytes(32, 'big') for value in values)
    accepted = verify(toolchain, journal, invocation, proof)
    for result in (produced, accepted):
        assert (result['execution']['return_at'] is not None) == (scenario == 'complete')
    trailing = directory / 'trailing-arm.bin'
    trailing.write_bytes(proof.read_bytes() + b'\xff')
    verify(toolchain, journal, invocation, trailing, 'artifact-stopped')
    if scenario != 'dormant':
        changed_public = journal.write('changed-arm-public.json', {**public, 'public': '50'})
        verify(toolchain, journal, [*args, f'--public={changed_public}'], proof, 'artifact-rejected')
        changed = directory / 'changed-arm-payload.bin'
        changed.write_bytes(bytes(32) + proof.read_bytes()[32:])
        verify(toolchain, journal, invocation, changed, 'artifact-rejected')
    if scenario == 'stop':
        stopped = {**public, 'enabled': False}
        prove(toolchain, journal, directory, args, stopped, 'arm-source-stop', 'artifact-stopped')
        stopped_public = journal.write('arm-stop-public.json', stopped)
        stop_args = [*args, f'--public={stopped_public}']
        original_stop = verify(toolchain, journal, stop_args, proof, 'artifact-stopped')
        malformed = directory / 'unreached-arm-response.bin'
        malformed.write_bytes(proof.read_bytes()[:64] + b'\xff')
        malformed_stop = verify(toolchain, journal, stop_args, malformed, 'artifact-stopped')
        for result in (original_stop, malformed_stop):
            assert result['execution']['stop']['role'] == VALIDATOR
            assert result['execution']['stop']['kind'] == 'Explicit("reject")'
            assert result['execution']['return_at'] is None
        assert original_stop['execution']['instructions'] < accepted['execution']['instructions']
        assert original_stop['execution']['instructions'] == malformed_stop['execution']['instructions']


@pytest.mark.parametrize('scenario', ['continue', 'complete', 'dormant', 'stop'])
def test_managed_keccak_selected_completion(toolchain, journal, directory, scenario):
    args = compile_source(toolchain, journal, directory, source_text('keccak'),
                          round_paths(CHOSEN), suite=KECCAK)
    public = public_values(choice=scenario != 'dormant',
                           finish=scenario in ('complete', 'dormant'))
    proof, invocation, produced = prove(toolchain, journal, directory, args, public)
    accepted = verify(toolchain, journal, invocation, proof)
    frame_count = 0 if scenario == 'dormant' else 2 if scenario == 'complete' else 4
    assert len(proof_frames(proof)) == frame_count
    for result in (produced, accepted):
        assert (result['execution']['return_at'] is not None) == (scenario == 'complete')
        transcript = [r for r in result['execution']['resources']
                      if r['kind'] == 'capability' and r['stage'] == 'transcript']
        assert len(transcript) == 1
        assert transcript[0]['transitions'] == (0 if scenario == 'dormant' else frame_count + 2)
    trailing = directory / 'keccak-trailing.bin'
    trailing.write_bytes(proof.read_bytes() + b'\xff')
    verify(toolchain, journal, invocation, trailing, 'proof-trailing')
    if scenario == 'stop':
        stopped = {**public, 'enabled': False}
        prove(toolchain, journal, directory, args, stopped, 'keccak-source-stop', 'artifact-stopped')
