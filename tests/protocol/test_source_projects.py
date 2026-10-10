"""Published .zkc library clients execute through the ordinary Entry Host."""
from input_files import input_files
import json
import os
from pathlib import Path
import re

import pytest

ROOT = Path(__file__).resolve().parents[2]


def read(project, group, entry='Proof'):
    path = ROOT / f'examples/projects/{project}/inputs/example.{entry}/{group}.json'
    return json.loads(path.read_text()) if path.exists() else {}


def build(toolchain, journal, directory, project, entry, flags):
    package = directory / f'{entry}.zkpkg'
    report = json.loads(journal.run([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
        f'--project={ROOT}/examples/projects/{project}/zkc.toml',
        f'example::{entry}', f'--output={package}', *flags]))
    return package, report['package_sha256']


@pytest.mark.parametrize('project', ['schnorr', 'sumcheck'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_library_entry_runs_and_independent_proofs(toolchain, journal, directory, project, flags):
    package, pin = build(toolchain, journal, directory, project, 'Proof', flags)
    producer = input_files(journal, 'producer', public=read(project, 'public'), witness=read(project, 'witness'))
    verifier = input_files(journal, 'verifier', public=read(project, 'public'))
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    report = json.loads(journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}']))
    assert report['status'] == 'accepted' and report['binding_scope'] == 'transcript'
    truncated = directory / 'truncated.bin'
    truncated.write_bytes(proof.read_bytes()[:-1])
    journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={truncated}'], refuses='proof-truncated')

    package, pin = build(toolchain, journal, directory, project, 'Interactive', flags)
    inputs = input_files(journal, 'interactive', roles={role: {'inputs': read(project, role, 'Interactive')} for role in ['P', 'V']})
    outputs = directory / 'outputs.json'
    report = json.loads(journal.run([toolchain.runtime, 'run', f'--package={package}', f'--sha256={pin}', *inputs, f'--results={outputs}']))
    assert report['status'] == 'executed'
    assert json.loads(outputs.read_text())['roles']['V']['accepted'] is True


@pytest.mark.parametrize('project', ['schnorr', 'sumcheck'])
def test_source_protocols_reject_false_inputs(toolchain, journal, directory, project):
    package, pin = build(toolchain, journal, directory, project, 'Proof', [])
    public, witness = read(project, 'public'), read(project, 'witness')
    if project == 'schnorr':
        # Canonical scalar 4 against the public point 3*G.
        witness['scalar'] = '4'
    else:
        # The first round is valid, but two table entries remain. The actual
        # terminal predicate must reject; returning a round claim is insufficient.
        public['rounds'] = '1'
    producer = input_files(journal, 'producer', public=public, witness=witness)
    verifier = input_files(journal, 'verifier', public=public)
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}'], refuses='artifact-rejected')


def test_sumcheck_uses_received_coefficients_and_actual_claim(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'sumcheck', 'Proof', [])
    public, witness = read('sumcheck', 'public'), {}
    public['claim'] = '11'
    producer = input_files(journal, 'producer', public=public, witness=witness)
    verifier = input_files(journal, 'verifier', public=public)
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    rejected = json.loads(journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}'], refuses='artifact-stopped'))
    assert rejected['execution']['stop']['role'] == 'V'
    assert rejected['execution']['stop']['kind'] == 'Explicit("reject")'
    producer = input_files(journal, 'producer', public=read('sumcheck', 'public'))
    verifier = input_files(journal, 'verifier', public=read('sumcheck', 'public'))
    journal.run([toolchain.runtime, 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    changed = bytearray(proof.read_bytes())
    changed[-32] ^= 1  # Canonical final coefficient, with its framing intact.
    proof.write_bytes(changed)
    journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}'], refuses='artifact-stopped')


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
