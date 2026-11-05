"""Execute checked 4.1 selected control through native export and the CPU Host.

Inputs satisfy the source's common-input requirements. Generic bundle execution
is distinct from the SDK's automatic source-interface input admission.
"""
import hashlib
import json
from pathlib import Path

import pytest

FIXTURES = Path(__file__).resolve().parents[3] / 'compiler/test/fixtures/selected-control'


def boolean(value):
    return b'ZKCV\x00\x05' + bytes([value])


def choice(alternative, *payload):
    return b'ZKCV\x00\x41' + alternative.to_bytes(4, 'little') + b''.join(
        len(value).to_bytes(4, 'little') + value for value in payload)


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('fixture', ['shared', 'math', 'match'])
def test_checked_source_selection_executes(toolchain, journal, directory, fixture, flags):
    source_flags = ['--source-format=zkc-layout', '--subject=selected::Run',
                    f'--module=selected={FIXTURES / (fixture + ".zkc")}']
    original = directory / 'original.mlir'
    original.write_text(journal.run([toolchain.compiler, 'language-emit', *source_flags]))
    interface = journal.json([toolchain.compiler, 'language-interface', *source_flags])
    bundle = directory / 'selected.bundle'
    bundle.write_text(journal.run([toolchain.compiler, 'protocol-bundle', original,
                                   f'--entry={interface["protocol"]}', *flags]))
    document = json.loads(bundle.read_text())
    program = json.loads(document['candidate'])
    participants = [function for function in program[3] if function[0] == 'participant']
    assert len(participants) == (1 if fixture == 'math' else 2)
    assert '"if"' in json.dumps(program) or '"match"' in json.dumps(program)
    examples = ([([choice(0, boolean(value))], value) for value in (False, True)] +
                [([choice(1)], False)] if fixture == 'match' else
                [([boolean(value), boolean(True), boolean(False)], value)
                 for value in (False, True)])
    for ordinal, (values, expected) in enumerate(examples):
        roles = []
        for function in participants:
            assert len(function[4]) == len(values)
            roles.append([function[3], [
                [str(index), port[1], ['wire', value.hex()]]
                for index, (port, value) in enumerate(zip(function[4], values))
            ], []])
        inputs = journal.write(f'inputs-{ordinal}.json', [
            'zkc.bundle-inputs/0', document['entry'], roles, [],
        ])
        result = journal.json([
            toolchain.runtime, '--json', 'bundle', 'run', bundle,
            hashlib.sha256(bundle.read_bytes()).hexdigest(), inputs, '--threads=1',
        ], keep=f'result-{ordinal}.json')
        assert result['outcome'] == ['completed'], result
        assert len(result['roles']) == len(participants)
        for role in result['roles']:
            assert role['active_frames'] == role['live_resource_units'] == 0
            assert [value[2] for value in role['outputs']] == [boolean(expected).hex()]


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_communicated_private_configuration_executes(toolchain, journal, directory, flags):
    source_flags = ['--source-format=zkc-layout', '--subject=selected::Run',
                    f'--module=selected={FIXTURES / "communicated.zkc"}']
    original = directory / 'original.mlir'
    original.write_text(journal.run([toolchain.compiler, 'language-emit', *source_flags]))
    interface = journal.json([toolchain.compiler, 'language-interface', *source_flags])
    root = next(item for item in interface['protocols'] if item['symbol'] == interface['protocol'])
    assert root['common_input_requirements'] == []
    bundle = directory / 'communicated.bundle'
    bundle.write_text(journal.run([toolchain.compiler, 'protocol-bundle', original,
                                   f'--entry={interface["protocol"]}', *flags]))
    document = json.loads(bundle.read_text())
    program = json.loads(document['candidate'])
    participants = [function for function in program[3] if function[0] == 'participant']
    assert len(participants) == 2
    # Only the actual sender has inputs; the other endpoint learns its control
    # values from the two payload components, including the loop's zero path.
    assert sorted(len(function[4]) for function in participants) == [0, 2]
    for count, enabled in [(0, False), (1, False), (3, True), (4, False)]:
        values = [b'ZKCV\x00\x1f' + count.to_bytes(8, 'little'), boolean(enabled)]
        roles = [[function[3], [
            [str(index), port[1], ['wire', value.hex()]]
            for index, (port, value) in enumerate(zip(function[4], values))
        ], []] for function in participants]
        inputs = journal.write(f'inputs-{count}-{enabled}.json', [
            'zkc.bundle-inputs/0', document['entry'], roles, [],
        ])
        result = journal.json([
            toolchain.runtime, '--json', 'bundle', 'run', bundle,
            hashlib.sha256(bundle.read_bytes()).hexdigest(), inputs, '--threads=1',
        ])
        assert result['outcome'] == ['completed'], result
        assert result['wire']['sends'] == result['wire']['receives'] == 2
        for role in result['roles']:
            assert role['active_frames'] == role['live_resource_units'] == 0
            assert [value[2] for value in role['outputs']] == [boolean(count > 0 and not enabled).hex()]


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_communicated_random_result_executes(toolchain, journal, directory, flags):
    source_flags = ['--source-format=zkc-layout', '--subject=selected::Run',
                    f'--module=selected={FIXTURES / "communicated-sample.zkc"}']
    original = directory / 'original.mlir'
    original.write_text(journal.run([toolchain.compiler, 'language-emit', *source_flags]))
    interface = journal.json([toolchain.compiler, 'language-interface', *source_flags])
    root = next(item for item in interface['protocols'] if item['symbol'] == interface['protocol'])
    assert root['common_input_requirements'] == []
    bundle = directory / 'communicated-sample.bundle'
    bundle.write_text(journal.run([toolchain.compiler, 'protocol-bundle', original,
                                   f'--entry={interface["protocol"]}', *flags]))
    document = json.loads(bundle.read_text())
    program = json.loads(document['candidate'])
    participants = [function for function in program[3] if function[0] == 'participant']
    assert len(participants) == 2
    assert all(function[4] == [] for function in participants)
    assert sorted(len(function[7]) for function in participants) == [0, 1]
    inputs = journal.write('inputs.json', [
        'zkc.bundle-inputs/0', document['entry'], [[function[3], [], [
            [str(index), service[1], '4'] for index, service in enumerate(function[7])
        ]] for function in participants], [],
    ])
    result = journal.json([
        toolchain.runtime, '--json', 'bundle', 'run', bundle,
        hashlib.sha256(bundle.read_bytes()).hexdigest(), inputs, '--threads=1',
    ])
    assert result['outcome'] == ['completed'], result
    outputs = [[value[2] for value in role['outputs']] for role in result['roles']]
    assert len(outputs[0]) == 2 and outputs[0][0] == boolean(True).hex()
    assert outputs[0] == outputs[1]
    assert [resource['state']['transitions'] for resource in result['resources']] == [1]
    assert all(role['active_frames'] == role['live_resource_units'] == 0
               for role in result['roles'])


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_communicated_control_keeps_recipient_scoped_stop(toolchain, journal, directory, flags):
    source_flags = ['--source-format=zkc-layout', '--subject=selected::Run',
                    f'--module=selected={FIXTURES / "communicated-stop.zkc"}']
    original = directory / 'original.mlir'
    original.write_text(journal.run([toolchain.compiler, 'language-emit', *source_flags]))
    interface = journal.json([toolchain.compiler, 'language-interface', *source_flags])
    root = next(item for item in interface['protocols'] if item['symbol'] == interface['protocol'])
    assert root['common_input_requirements'] == []
    bundle = directory / 'communicated-stop.bundle'
    bundle.write_text(journal.run([toolchain.compiler, 'protocol-bundle', original,
                                   f'--entry={interface["protocol"]}', *flags]))
    document = json.loads(bundle.read_text())
    participants = [function for function in json.loads(document['candidate'])[3]
                    if function[0] == 'participant']
    assert [len(function[4]) for function in participants] == [1, 0]
    for flag in (True, False):
        inputs = journal.write(f'inputs-{flag}.json', [
            'zkc.bundle-inputs/0', document['entry'], [[function[3], [
                [str(index), port[1], ['wire', boolean(flag).hex()]]
                for index, port in enumerate(function[4])
            ], []] for function in participants], [],
        ])
        result = journal.json([
            toolchain.runtime, '--json', 'bundle', 'run', bundle,
            hashlib.sha256(bundle.read_bytes()).hexdigest(), inputs, '--threads=1',
        ], refuses=None if flag else 'participant-stopped')
        assert result['outcome'] == (['completed'] if flag else ['participant-stopped', 1])
        if flag:
            assert all([value[2] for value in role['outputs']] == [boolean(True).hex()]
                       for role in result['roles'])
        else:
            assert result['roles'][1]['outputs'] == []
        assert all(role['active_frames'] == role['live_resource_units'] == 0
                   for role in result['roles'])


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_communicated_prefix_preserves_partial_delivery(toolchain, journal, directory, flags):
    source_flags = ['--source-format=zkc-layout', '--subject=selected::Run',
                    f'--module=selected={FIXTURES / "communicated-prefix.zkc"}']
    original = directory / 'original.mlir'
    original.write_text(journal.run([toolchain.compiler, 'language-emit', *source_flags]))
    interface = journal.json([toolchain.compiler, 'language-interface', *source_flags])
    root = next(item for item in interface['protocols'] if item['symbol'] == interface['protocol'])
    assert root['common_input_requirements'] == []
    bundle = directory / 'communicated-prefix.bundle'
    bundle.write_text(journal.run([toolchain.compiler, 'protocol-bundle', original,
                                   f'--entry={interface["protocol"]}', *flags]))
    document = json.loads(bundle.read_text())
    participants = [function for function in json.loads(document['candidate'])[3]
                    if function[0] == 'participant']
    assert [len(function[4]) for function in participants] == [1, 0, 1]
    for go in (True, False):
        inputs = journal.write(f'inputs-{go}.json', [
            'zkc.bundle-inputs/0', document['entry'], [[function[3], [
                [str(index), port[1], ['wire', boolean(True if role == 0 else go).hex()]]
                for index, port in enumerate(function[4])
            ], []] for role, function in enumerate(participants)], [],
        ])
        result = journal.json([
            toolchain.runtime, '--json', 'bundle', 'run', bundle,
            hashlib.sha256(bundle.read_bytes()).hexdigest(), inputs, '--threads=1',
        ], refuses=None if go else 'participant-stopped')
        assert result['outcome'] == (['completed'] if go else ['participant-stopped', 2])
        assert result['wire']['sends'] == result['wire']['receives'] == (2 if go else 1)
        deliveries = [event for event in result['reached']
                      if event['receive_completion'] == 'Delivered']
        assert [event['role'] for event in deliveries] == ([1, 2] if go else [1])
        if go:
            assert all([value[2] for value in role['outputs']] == [boolean(True).hex()]
                       for role in result['roles'])
        else:
            assert result['roles'][2]['outputs'] == []
        assert all(role['active_frames'] == role['live_resource_units'] == 0
                   for role in result['roles'])
