"""Independent library clients must discharge each returned evaluation."""

import json

import pytest

from input_files import input_files
from test_source_projects import build, read


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_composed_sumchecks(toolchain, journal, directory, flags):
    package, pin = build(toolchain, journal, directory, 'composed-sumcheck', 'Proof', flags)
    public = read('composed-sumcheck', 'public')
    request = input_files(journal, 'public', public=public)
    proof = directory / 'proof.bin'
    args = [f'--package={package}', f'--sha256={pin}', *request]
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'])
    checked = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert checked['status'] == 'accepted'
    assert produced['execution']['messages'] == 8


@pytest.mark.parametrize('changed', ['left', 'right'])
def test_each_obligation_uses_its_own_verifier_table(toolchain, journal, directory, changed):
    package, pin = build(toolchain, journal, directory, 'composed-sumcheck', 'Interactive', [])
    public = read('composed-sumcheck', 'public')
    prover = {name: public[name] for name in ('left', 'right', 'rounds')}
    verifier = dict(public)
    verifier[changed] = ['0'] * 4
    inputs = input_files(journal, 'interactive', roles={
        'P': {'inputs': prover}, 'V': {'inputs': verifier}})
    outputs = directory / 'outputs.json'
    journal.run([toolchain.runtime, '--json', 'run', f'--package={package}',
                 f'--sha256={pin}', *inputs, f'--results={outputs}'])
    assert json.loads(outputs.read_text())['roles']['V']['accepted'] is False


@pytest.mark.parametrize('rounds,table,claim,accepted', [
    (0, ['7'], '7', True),
    (0, ['7'], '8', False),
    (0, [], '0', False),
    (1, ['1', '2', '3', '4'], '10', False),
])
def test_public_sumcheck_terminal_dimension(toolchain, journal, directory, rounds, table, claim, accepted):
    package, pin = build(toolchain, journal, directory, 'sumcheck', 'Interactive', [])
    public = {'values': table, 'claim': claim, 'rounds': str(rounds)}
    inputs = input_files(journal, 'interactive', roles={
        'P': {'inputs': {'values': table, 'rounds': str(rounds)}},
        'V': {'inputs': public}})
    outputs = directory / 'outputs.json'
    journal.run([toolchain.runtime, '--json', 'run', f'--package={package}',
                 f'--sha256={pin}', *inputs, f'--results={outputs}'])
    assert json.loads(outputs.read_text())['roles']['V']['accepted'] is accepted


def test_reduction_retains_actual_point_and_prover_residual(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'composed-sumcheck', 'Reduction', [])
    inputs = input_files(journal, 'interactive', roles={
        'P': {'inputs': {'values': ['1', '2', '3', '4'], 'rounds': '2'}},
        'V': {'inputs': {'claim': '10', 'rounds': '2'}}})
    outputs = directory / 'outputs.json'
    journal.run([toolchain.runtime, '--json', 'run', f'--package={package}',
                 f'--sha256={pin}', *inputs, f'--results={outputs}'])
    result = json.loads(outputs.read_text())['roles']
    assert result['P']['point'] == result['V']['evaluation']['point']
    assert len(result['P']['point']) == 2
    assert result['P']['residual'] == [result['V']['evaluation']['value']]
