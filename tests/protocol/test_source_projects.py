"""Published .zkc library clients execute through the ordinary Entry Host."""
import json
import os
from pathlib import Path
import re

import pytest

ROOT = Path(__file__).resolve().parents[2]


def read(project, name):
    return json.loads((ROOT / f'examples/projects/{project}/{name}.json').read_text())


def request(directory, name, value):
    path = directory / name
    path.write_text(json.dumps(value))
    return path


def build(toolchain, journal, directory, project, entry, flags):
    package = directory / f'{entry}.entry'
    report = json.loads(journal.run([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
        f'--project={ROOT}/examples/projects/{project}/zkc.json',
        f'--entry=example::{entry}', f'--output={package}', *flags]))
    return package, report['package_sha256']


@pytest.mark.parametrize('project', ['schnorr', 'sumcheck'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_library_entry_runs_and_independent_proofs(toolchain, journal, directory, project, flags):
    package, pin = build(toolchain, journal, directory, project, 'Proof', flags)
    producer = request(directory, 'producer.json', read(project, 'prover'))
    verifier = request(directory, 'verifier.json', read(project, 'verifier'))
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    report = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, verifier, proof]))
    assert report['status'] == 'accepted' and report['binding_scope'] == 'transcript'
    truncated = directory / 'truncated.bin'
    truncated.write_bytes(proof.read_bytes()[:-1])
    journal.run([toolchain.runtime, 'verify', package, pin, verifier, truncated], refuses='proof-truncated')

    package, pin = build(toolchain, journal, directory, project, 'Interactive', flags)
    inputs = request(directory, 'interactive.json', read(project, 'interactive'))
    outputs = directory / 'outputs.json'
    report = json.loads(journal.run([toolchain.runtime, 'run', package, pin, inputs, f'--results={outputs}']))
    assert report['status'] == 'executed'
    assert json.loads(outputs.read_text())['roles']['V']['accepted'] is True


@pytest.mark.parametrize('project', ['schnorr', 'sumcheck'])
def test_source_protocols_reject_false_inputs(toolchain, journal, directory, project):
    package, pin = build(toolchain, journal, directory, project, 'Proof', [])
    producer_value, verifier_value = read(project, 'prover'), read(project, 'verifier')
    if project == 'schnorr':
        # Canonical scalar 4 against the public point 3*G.
        producer_value['inputs']['scalar'] = (b'ZKCV\x00\x01' + (4).to_bytes(32, 'little')).hex()
    else:
        # The first round is valid, but two table entries remain. The actual
        # terminal predicate must reject; returning a round claim is insufficient.
        producer_value['public']['rounds'] = verifier_value['public']['rounds'] = 1
    producer = request(directory, 'producer.json', producer_value)
    verifier = request(directory, 'verifier.json', verifier_value)
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    journal.run([toolchain.runtime, 'verify', package, pin, verifier, proof], refuses='artifact-rejected')


def test_sumcheck_uses_received_coefficients_and_actual_claim(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'sumcheck', 'Proof', [])
    producer_value, verifier_value = read('sumcheck', 'prover'), read('sumcheck', 'verifier')
    wrong = (b'ZKCV\x00\x01' + (11).to_bytes(32, 'little')).hex()
    producer_value['public']['claim'] = verifier_value['public']['claim'] = wrong
    producer = request(directory, 'producer.json', producer_value)
    verifier = request(directory, 'verifier.json', verifier_value)
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    rejected = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, verifier, proof], refuses='artifact-stopped'))
    assert rejected['execution']['stop']['role'] == 'V'
    assert rejected['execution']['stop']['kind'] == 'Explicit("reject")'
    producer.write_text(json.dumps(read('sumcheck', 'prover')))
    verifier.write_text(json.dumps(read('sumcheck', 'verifier')))
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    changed = bytearray(proof.read_bytes())
    changed[-32] ^= 1  # Canonical final coefficient, with its framing intact.
    proof.write_bytes(changed)
    journal.run([toolchain.runtime, 'verify', package, pin, verifier, proof], refuses='artifact-stopped')


def test_published_source_walkthrough(toolchain, journal, directory):
    text = (ROOT / 'docs/getting-started.md').read_text()
    block = re.search(r'<!-- executable: source-proof -->\s*```sh\n(.*?)\n```', text, re.S)
    assert block, 'the published source walkthrough is missing'
    cargo = directory / 'cargo target'
    cargo.mkdir()
    (cargo / 'release').symlink_to(toolchain.directories['native'], target_is_directory=True)
    env = dict(os.environ, TMPDIR=str(directory), CARGO_TARGET_DIR=str(cargo),
               ZKC_COMPILER_BIN=str(toolchain.directories['compiler']))
    env.pop('ZKC_NATIVE_BIN', None)
    # No Lean executable or prover state is needed by this published path.
    env['ZKC_LEAN_BIN'] = str(directory / 'absent-lean')
    result = journal.attempt(['bash', '-euo', 'pipefail', '-c', block[1]], cwd=ROOT, env=env)
    assert result.returncode == 0, result.stdout + result.stderr
    output = Path(result.stdout.rsplit('Demo files: ', 1)[1].strip())
    assert output.parent == directory
    producer = json.loads((output / 'producer.json').read_text())
    verifier = json.loads((output / 'validator.json').read_text())
    assert producer['status'] == 'produced' and verifier['status'] == 'accepted'
    assert (output / 'proof.bin').stat().st_size == producer['proof_bytes']
