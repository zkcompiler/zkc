"""Independent library clients must discharge each returned evaluation."""

import json

import pytest

from entry import joint_execution

from input_files import input_files
from test_source_projects import build, read


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_composed_sumchecks(toolchain, journal, directory, flags):
    package, pin = build(toolchain, journal, directory, 'examples/projects/sumcheck/composed', 'Proof', flags)
    public = read('examples/projects/sumcheck/composed', 'public')
    request = input_files(journal, 'public', public=public)
    proof = directory / 'proof.bin'
    args = [f'--package={package}', f'--sha256={pin}', *request]
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'])
    checked = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert checked['status'] == 'accepted'
    assert produced['execution']['messages'] == 8


@pytest.mark.parametrize('changed', ['left', 'right'])
def test_each_obligation_uses_its_own_verifier_table(toolchain, journal, directory, changed):
    package, pin = build(toolchain, journal, directory, 'examples/projects/sumcheck/composed', 'Interactive', [])
    public = read('examples/projects/sumcheck/composed', 'public')
    prover = {name: public[name] for name in ('left', 'right', 'rounds')}
    verifier = dict(public)
    verifier[changed] = ['0'] * 4
    inputs = input_files(journal, 'interactive', package=package, arguments={'inputs': {'P': prover, 'V': verifier}})
    outputs = directory / 'outputs.json'
    journal.run([toolchain.runtime, '--json', 'run', f'--package={package}',
                 f'--sha256={pin}', *inputs, f'--results={outputs}'])
    assert json.loads(outputs.read_text())['value']['V']['accepted'] is False


@pytest.mark.parametrize('rounds,table,claim,accepted', [
    (0, ['7'], '7', True),
    (0, ['7'], '8', False),
    (0, [], '0', False),
    (1, ['1', '2', '3', '4'], '10', False),
])
def test_public_sumcheck_terminal_dimension(toolchain, journal, directory, rounds, table, claim, accepted):
    package, pin = build(toolchain, journal, directory, 'examples/projects/sumcheck', 'Interactive', [])
    public = {'values': table, 'claim': claim, 'rounds': str(rounds)}
    inputs = input_files(journal, 'interactive', package=package, arguments={'inputs': {'P': {'values': table, 'rounds': str(rounds)}, 'V': public}})
    outputs = directory / 'outputs.json'
    malformed = len(table) != 2 ** rounds
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={pin}', *inputs, f'--results={outputs}'],
                          refuses='entry-host-run-failed' if malformed else None)
    if malformed:
        assert joint_execution(report)['wire']['sends'] == 0
        assert not outputs.exists()
    else:
        assert json.loads(outputs.read_text())['value']['V']['accepted'] is accepted



@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
@pytest.mark.parametrize('table', [[], ['3', '7'], ['1', '0', '2', '0', '3', '0', '4', '0']])
def test_sumcheck_rejects_only_the_verifier_table(toolchain, journal, directory, flags, table):
    # The padded table leaves [P(r1,r2), 0] after the two MSB-first folds.
    # Its residual sum agrees, so only complete dimension discharge rejects it.
    package, pin = build(toolchain, journal, directory, 'examples/projects/sumcheck', 'Interactive', flags)
    inputs = input_files(journal, 'interactive', package=package, arguments={'inputs': {'P': {'values': ['1', '2', '3', '4'], 'rounds': '2'}, 'V': {'values': table, 'claim': '10', 'rounds': '2'}}})
    outputs = directory / 'outputs.json'
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={pin}', *inputs, f'--results={outputs}'])
    # Each round sends two boundary sums and one delivered challenge.
    assert joint_execution(report)['wire']['sends'] == 6
    assert json.loads(outputs.read_text())['value']['V']['accepted'] is False


@pytest.mark.parametrize('rounds', [0, 1, 2])
def test_reduction_retains_actual_point_and_prover_residual(toolchain, journal, directory, rounds):
    package, pin = build(toolchain, journal, directory, 'examples/projects/sumcheck/composed', 'Reduction', [])
    inputs = input_files(journal, 'interactive', package=package, arguments={'inputs': {'P': {'values': ['1', '2', '3', '4'], 'variables': '2', 'rounds': str(rounds)}, 'V': {'claim': '10', 'rounds': str(rounds)}}})
    outputs = directory / 'outputs.json'
    journal.run([toolchain.runtime, '--json', 'run', f'--package={package}',
                 f'--sha256={pin}', *inputs, f'--results={outputs}'])
    result = json.loads(outputs.read_text())['value']
    assert result['P']['point'] == result['V']['evaluation']['point']
    assert len(result['P']['point']) == rounds
    # Independent MSB-first interpolation of each remaining Boolean row.
    modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    residual = [1, 2, 3, 4]
    for coordinate in map(int, result['V']['evaluation']['point']):
        half = len(residual) // 2
        residual = [(1-coordinate) * low + coordinate * high
                    for low, high in zip(residual[:half], residual[half:], strict=True)]
    assert int(result['V']['evaluation']['value']) == sum(residual) % modulus
    assert list(map(int, result['P']['residual'])) == [x % modulus for x in residual]


def test_reduction_rejects_excess_rounds_before_sending(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'examples/projects/sumcheck/composed', 'Reduction', [])
    inputs = input_files(journal, 'interactive', package=package, arguments={'inputs': {'P': {'values': ['1', '2', '3', '4'], 'variables': '2', 'rounds': '3'}, 'V': {'claim': '10', 'rounds': '3'}}})
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={pin}', *inputs], refuses='entry-host-run-failed')
    assert joint_execution(report)['wire']['sends'] == 0


def test_proof_binds_public_tables_even_with_unchanged_sum(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'examples/projects/sumcheck/composed', 'Proof', [])
    public = read('examples/projects/sumcheck/composed', 'public')
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
    package, pin = build(toolchain, journal, directory, 'common/tests/fixtures/projects/polynomial-opening', 'Proof', flags)
    public = read('common/tests/fixtures/projects/polynomial-opening', 'public')
    witness = read('common/tests/fixtures/projects/polynomial-opening', 'witness')
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
    package, pin = build(toolchain, journal, directory, 'common/tests/fixtures/projects/polynomial-opening', 'Proof', [])
    public = read('common/tests/fixtures/projects/polynomial-opening', 'public')
    public['point'] = public['shift']
    producer = input_files(journal, 'pole', public=public,
                           witness=read('common/tests/fixtures/projects/polynomial-opening', 'witness'))
    journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}',
                 f'--sha256={pin}', *producer, f'--output={directory / "pole.proof"}'],
                refuses=True)


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_constructed_schnorr_uses_generic_protocol_and_external_bytes(toolchain, journal, directory, flags):
    package, pin = build(toolchain, journal, directory, 'examples/projects/schnorr/spongefish', 'Proof', flags)
    public = read('examples/projects/schnorr/spongefish', 'public')
    public_path = journal.write('public.json', public)
    witness_path = journal.write('witness.json', read('examples/projects/schnorr/spongefish', 'witness'))
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
    package, pin = build(toolchain, journal, directory, 'common/tests/fixtures/projects/polynomial-opening', 'Interactive', [])
    public = read('common/tests/fixtures/projects/polynomial-opening', 'public')
    witness = read('common/tests/fixtures/projects/polynomial-opening', 'witness')
    roles = {'P': public | witness, 'V': dict(public)}
    roles[role]['point'] = public['shift']
    request = input_files(journal, 'pole', package=package, arguments={'inputs': roles})
    refused = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                            f'--sha256={pin}', *request, f'--results={directory / "outputs.json"}'],
                           refuses='entry-host-run-failed')
    stopped = joint_execution(refused)['roles'][0 if role == 'P' else 1]['after']
    assert stopped[0] == 'stopped'
    assert stopped[1]['cause'] == ['explicit', {'text': 'reject', 'omitted_bytes': 0}]


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_residual_view_composes_two_partial_reductions(toolchain, journal, directory, flags):
    from entry import Entry
    from source_modules import library_modules

    source = '''module sample;
use zkc::multilinear as mle;
use zkc::vector as vec;
use sumcheck::{Reduce};
domain F=field("bls12-381.fr");
protocol Run roles(P,V)(values:vec::Vector<F>@P,claim:F@V,challenges:Random<F>@V)
 ->(point:vec::Vector<F>@P,residual:vec::Vector<F>@P,remaining:index@P,value:F@V){
 let table=mle::table(values,2,1);
 let (p0,residual0,e0)=Reduce<F,2>(table,claim,1,challenges);
 let (p1,residual1,e1)=Reduce<F,2>(residual0,e0.value,1,challenges);
 return(point=vec::concat(p0,p1),residual=mle::values(residual1),
        remaining=mle::variables(residual1),value=e1.value);
}entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, (*library_modules('protocols/polynomial/sumcheck'), *flags))
    result = entry.run_roles('two-prefixes', {
        'P': {'values': ['1', '2', '3', '4']},
        'V': {'claim': '10'}})
    r0, r1 = map(int, result['P']['point'])
    modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
    expected = ((1-r0)*(1-r1) + 2*(1-r0)*r1 + 3*r0*(1-r1) + 4*r0*r1) % modulus
    assert result['P']['remaining'] == '0'
    assert result['P']['residual'] == [str(expected)]
    assert result['V']['value'] == str(expected)
