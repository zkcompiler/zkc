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
    # Independent MSB-first interpolation, without using the library fold.
    modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    r0, r1 = map(int, result['V']['evaluation']['point'])
    expected = (1 * (1-r0) * (1-r1) + 2 * (1-r0) * r1
                + 3 * r0 * (1-r1) + 4 * r0 * r1) % modulus
    assert int(result['V']['evaluation']['value']) == expected
    assert result['P']['residual'] == [result['V']['evaluation']['value']]


def test_proof_binds_public_tables_even_with_unchanged_sum(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'composed-sumcheck', 'Proof', [])
    public = read('composed-sumcheck', 'public')
    request = input_files(journal, 'original', public=public)
    proof = directory / 'proof.bin'
    args = [f'--package={package}', f'--sha256={pin}']
    journal.run([toolchain.runtime, '--json', 'prove', *args, *request, f'--output={proof}'])
    public['left'] = list(reversed(public['left']))
    changed = input_files(journal, 'changed', public=public)
    journal.run([toolchain.runtime, '--json', 'verify', *args, *changed,
                 f'--proof={proof}'], refuses='proof-header')


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk']])
def test_opening_composes_shared_equations_and_fri(toolchain, journal, directory, flags):
    package, pin = build(toolchain, journal, directory, 'polynomial-opening', 'Proof', flags)
    public = read('polynomial-opening', 'public')
    witness = read('polynomial-opening', 'witness')
    producer = input_files(journal, 'producer', public=public, witness=witness)
    verifier = input_files(journal, 'verifier', public=public)
    proof = directory / 'proof.bin'
    args = [f'--package={package}', f'--sha256={pin}']
    journal.run([toolchain.runtime, '--json', 'prove', *args, *producer, f'--output={proof}'])
    assert journal.json([toolchain.runtime, '--json', 'verify', *args, *verifier,
                         f'--proof={proof}'])['status'] == 'accepted'
    # The committed word is unchanged but the claimed value is false. A new
    # transcript cannot make the quotient a low-degree polynomial.
    public['value'][0] = str(int(public['value'][0]) + 1)
    producer = input_files(journal, 'false-producer', public=public, witness=witness)
    verifier = input_files(journal, 'false-verifier', public=public)
    wrong = directory / 'wrong.proof'
    journal.run([toolchain.runtime, '--json', 'prove', *args, *producer, f'--output={wrong}'])
    journal.run([toolchain.runtime, '--json', 'verify', *args, *verifier,
                 f'--proof={wrong}'], refuses='artifact-stopped')


def test_opening_refuses_a_pole_on_the_evaluation_domain(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'polynomial-opening', 'Proof', [])
    public = read('polynomial-opening', 'public')
    public['point'] = public['shift']
    producer = input_files(journal, 'pole', public=public,
                           witness=read('polynomial-opening', 'witness'))
    journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}',
                 f'--sha256={pin}', *producer, f'--output={directory / "pole.proof"}'],
                refuses=True)


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_constructed_schnorr_uses_generic_protocol_and_external_bytes(toolchain, journal, directory, flags):
    package, pin = build(toolchain, journal, directory, 'constructed-schnorr', 'Proof', flags)
    public = read('constructed-schnorr', 'public')
    public_path = journal.write('public.json', public)
    witness_path = journal.write('witness.json', read('constructed-schnorr', 'witness'))
    verifier = [f'--public={public_path}']
    producer = [*verifier, f'--witness={witness_path}']
    proof = directory / 'schnorr.proof'
    args = [f'--package={package}', f'--sha256={pin}', '--allow-authored']
    journal.run([toolchain.runtime, '--json', 'prove', *args, *producer, f'--output={proof}'])
    assert len(proof.read_bytes()) == 80
    assert journal.json([toolchain.runtime, '--json', 'verify', *args, *verifier,
                         f'--proof={proof}'])['status'] == 'accepted'
    assert journal.json([toolchain.driver('spongefish_schnorr'), 'verify', proof])['accepted']
    trailing = directory / 'trailing.proof'
    trailing.write_bytes(proof.read_bytes() + b'\x00')
    journal.run([toolchain.runtime, '--json', 'verify', *args, *verifier,
                 f'--proof={trailing}'], refuses='artifact-stopped')


@pytest.mark.parametrize('role', ['P', 'V'])
def test_each_opening_participant_checks_its_own_domain(toolchain, journal, directory, role):
    package, pin = build(toolchain, journal, directory, 'polynomial-opening', 'Interactive', [])
    public = read('polynomial-opening', 'public')
    witness = read('polynomial-opening', 'witness')
    roles = {'P': {'inputs': public | witness}, 'V': {'inputs': dict(public)}}
    roles[role]['inputs']['point'] = public['shift']
    request = input_files(journal, 'pole', roles=roles)
    refused = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                            f'--sha256={pin}', *request, f'--results={directory / "outputs.json"}'],
                           refuses='entry-run-incomplete')
    stopped = refused['execution']['roles'][0 if role == 'P' else 1]['after']
    assert stopped[0] == 'stopped'
    assert stopped[1]['cause'] == ['explicit', {'text': 'reject', 'omitted_bytes': 0}]
