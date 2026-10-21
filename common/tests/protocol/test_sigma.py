"""Published Sigma Entries and independent shared-challenge equation controls."""

import json

import pytest
from input_files import input_files
from sigma_reference import accepts, multiply, point
from test_source_projects import ROOT, build, read

PROJECT = 'examples/projects/sigma'


@pytest.mark.parametrize('kind', ['And', 'Equality'])
def test_published_sigma_entries(toolchain, journal, directory, kind):
    package, pin = build(toolchain, journal, directory, PROJECT, kind + 'Interactive', [])
    roles = {role: read(PROJECT, role, kind + 'Interactive') for role in ('P', 'V')}
    public = roles['V']
    generator = point(public['first_base'])
    assert point(public['first_point']) == multiply(generator, 3)
    assert point(public['second_base']) == multiply(generator, 5)
    assert point(public['second_point']) == multiply(generator, 35 if kind == 'And' else 15)
    inputs = input_files(journal, 'interactive', package=package, arguments={'inputs': roles})
    outputs = directory / 'outputs.json'
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={pin}', *inputs, f'--results={outputs}'])
    assert report['status'] == 'executed'
    assert json.loads(outputs.read_text())['value']['V']['accepted'] is True

    entry = kind + 'Proof'
    package, pin = build(toolchain, journal, directory, PROJECT, entry, [])
    public, witness = read(PROJECT, 'public', entry), read(PROJECT, 'witness', entry)
    proof = directory / 'proof.bin'
    args = [f'--package={package}', f'--sha256={pin}']
    producer = input_files(journal, 'producer', public=public, witness=witness)
    verifier = input_files(journal, 'verifier', public=public)
    journal.json([toolchain.runtime, '--json', 'prove', *args, *producer, f'--output={proof}'])
    verify = [toolchain.runtime, '--json', 'verify', *args, *verifier, f'--proof={proof}']
    assert journal.json(verify)['status'] == 'accepted'
    original = proof.read_bytes()
    # A canonical response change leaves framing and group decoding valid.
    proof.write_bytes(original[:-32] + bytes(32))
    journal.json(verify, refuses='artifact-rejected')
    proof.write_bytes(original)
    wrong = dict(witness)
    wrong['first_scalar' if kind == 'And' else 'scalar'] = '4'
    invalid = input_files(journal, 'wrong-witness', public=public, witness=wrong)
    journal.json([toolchain.runtime, '--json', 'prove', *args, *invalid, f'--output={proof}'])
    journal.json(verify, refuses='artifact-rejected')
    proof.write_bytes(original)
    wrong = dict(public, first_point=public['first_base'])
    invalid = input_files(journal, 'wrong-point', public=wrong)
    journal.json([toolchain.runtime, '--json', 'verify', *args, *invalid,
                  f'--proof={proof}'], refuses='proof-header')


@pytest.mark.parametrize('kind', ['And', 'Equality'])
@pytest.mark.parametrize('change', ['valid', 'point', 'witness', 'response', 'challenge'])
def test_sigma_equations_against_independent_reference(toolchain, journal, directory, kind, change):
    # Retain the library equations and actual message schedule. Expose service
    # results as role-owned inputs to compare deterministic equations separately
    # from managed randomness and Fiat-Shamir (covered by the published Entries).
    source = (ROOT / 'libraries/protocols/sigma/compositions/lib.zkc').read_text()
    source = source.replace('nonces: Random<G::Scalar> @P, challenges: Random<G::Scalar> @V',
                            'first_nonce: G::Scalar @P, second_nonce: G::Scalar @P, '
                            'nonce: G::Scalar @P, challenge: G::Scalar @V')
    for name in ('first_nonce', 'second_nonce', 'nonce'):
        source = source.replace(f'let {name} = nonces.draw();', '')
    source = source.replace('#[site(challenge)] let challenge = challenges.draw();', '')
    if change == 'response':
        source = source.replace('first_nonce + received * first_scalar', 'first_nonce + received * first_scalar + 1')
        source = source.replace('nonce + received * scalar', 'nonce + received * scalar + 1')
    if change == 'challenge':
        source = source.replace('send V -> P(challenge)', 'send V -> P(challenge + 1)')
    library = directory / 'sigma.zkc'
    library.write_text(source)
    client = directory / 'client.zkc'
    protocol = 'SchnorrAnd' if kind == 'And' else 'ChaumPedersen'
    client.write_text(f'''module example;
domain G=group("bls12-381.g1");
run Demo(inputs: sigma::{protocol}<G>::Inputs) {{ return sigma::{protocol}<G>::run(inputs); }}
''')
    package = directory / 'fixed.zkpkg'
    entry = kind + 'Interactive'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sigma={library}', f'--module=example={client}',
                             'example::Demo', f'--output={package}'])
    roles = {role: read(PROJECT, role, entry) for role in ('P', 'V')}
    roles['P'].update(first_nonce='11', second_nonce='13', nonce='11')
    roles['V']['challenge'] = '17'
    if change == 'point':
        for role in roles.values():
            role['first_point'] = role['first_base']
    if change == 'witness':
        roles['P']['first_scalar' if kind == 'And' else 'scalar'] = '4'
    witness = roles['P']
    scalars = ([int(witness['first_scalar']), int(witness['second_scalar'])] if kind == 'And'
               else [int(witness['scalar'])] * 2)
    expected = accepts(roles['V'], scalars, [11, 13] if kind == 'And' else [11, 11],
                       delivered=18 if change == 'challenge' else 17,
                       response_delta=int(change == 'response'))
    assert expected == (change == 'valid')
    inputs = input_files(journal, 'fixed', package=package, arguments={'inputs': roles})
    outputs = directory / 'fixed.json'
    journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                  f'--sha256={compiled["package_sha256"]}', *inputs, f'--results={outputs}'])
    assert json.loads(outputs.read_text())['value']['V']['accepted'] == expected
