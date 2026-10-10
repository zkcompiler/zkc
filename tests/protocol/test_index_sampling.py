"""A maintained source client samples verifier positions through managed services.

The spot check commits P's rows, samples UniformIndex(8) at V, and checks the
authenticated opening at that position. The proof Entry derives each position
from the native transcript; the run Entry draws it from V's managed service.
"""

from input_files import input_files
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CLIENT = ROOT / 'compiler/test/fixtures/language/index_sampling.zkc'
ROWS = [[i + 1, 2 * i, 0, 0, 0, 0, 0, 7] for i in range(8)]
SHIFTED = [[i + 2, 2 * i, 0, 0, 0, 0, 0, 7] for i in range(8)]


def vector(rows):
    return [[str(x) for x in row] for row in rows]


def compile_entry(toolchain, journal, directory, entry, flags=()):
    package = directory / f'{entry}.zkpkg'
    report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=sample={CLIENT}', f'sample::{entry}',
                           f'--output={package}', *flags])
    assert report['status'] == 'compiled'
    return package, report['package_sha256']


def write(path, value):
    path.write_text(json.dumps(value))
    return path


def write_bytes(path, value):
    path.write_bytes(bytes(value))
    return path


def requests(journal, directory, rows=ROWS, rounds=3, name='honest'):
    public = {'expected': vector(ROWS), 'rounds': rounds}
    producer = input_files(journal, (directory / f'{name}.producer.json').name, public=public, witness={'values': vector(rows)})
    verifier = input_files(journal, (directory / f'{name}.verifier.json').name, public=public, witness={})
    return producer, verifier


def frames(proof):
    """Offsets and payloads of the framed messages after the 40-byte header."""
    at, result = 40, []
    while at < len(proof):
        size = int.from_bytes(proof[at:at + 8], 'little')
        result.append((at + 8, proof[at + 8:at + 8 + size]))
        at += 8 + size
    assert at == len(proof)
    return result


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_derived_positions_prove_and_verify(toolchain, journal, directory, flags):
    package, pin = compile_entry(toolchain, journal, directory, 'Proof', flags)
    producer, verifier = requests(journal, directory)
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    assert produced['status'] == 'produced'
    # Five ordered transitions per round: root, index, delivery, row and path.
    transcript = [r for r in produced['execution']['resources'] if r['stage'] == 'transcript']
    assert transcript[0]['transitions'] == 15
    accepted = journal.json([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}'])
    assert accepted['status'] == 'accepted' and accepted['binding_scope'] == 'transcript'
    # Root, row and path per round; the sampled positions are never sent.
    assert len(frames(proof.read_bytes())) == 9


def test_altered_rows_proofs_and_statements_are_refused(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Proof')
    producer, verifier = requests(journal, directory)
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    original = proof.read_bytes()

    # Every committed row differs from V's copy, so every sampled position fails.
    shifted, _ = requests(journal, directory, SHIFTED, name='shifted')
    wrong = directory / 'wrong.bin'
    journal.run([toolchain.runtime, 'prove', f'--package={package}', f'--sha256={pin}', *shifted, f'--output={wrong}'])
    journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={wrong}'], refuses='artifact-stopped')

    # Change one coordinate of the first opened row, keeping it canonical.
    offset, payload = frames(original)[1]
    assert payload[:6] == b'ZKCV\x00\x1b'
    changed = bytearray(original)
    changed[offset + 10] ^= 1
    altered = write_bytes(directory / 'altered.bin', changed)
    journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={altered}'], refuses='artifact-stopped')
    truncated = write_bytes(directory / 'truncated.bin', original[:-1])
    journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={truncated}'], refuses='proof-truncated')

    # The public statement seeds the transcript; another round count is refused.
    _, other = requests(journal, directory, rounds=2, name='fewer')
    journal.run([toolchain.runtime, 'verify', f'--package={package}', f'--sha256={pin}', *other, f'--proof={proof}'], refuses='proof-header')


def test_managed_service_positions_run(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Interactive')
    def run(rows, name, refuses=None):
        request = input_files(journal, (directory / f'{name}.json').name, session='index_sampling', roles={'P': {'inputs': {'values': vector(rows), 'rounds': 3}},
                      'V': {'inputs': {'expected': vector(ROWS), 'rounds': 3}}})
        outputs = directory / f'{name}.outputs.json'
        report = journal.json([toolchain.runtime, 'run', f'--package={package}', f'--sha256={pin}', *request, f'--results={outputs}'], refuses=refuses)
        return report, outputs
    report, outputs = run(ROWS, 'honest')
    assert report['status'] == 'executed'
    assert json.loads(outputs.read_text())['roles']['V']['accepted'] is True
    report, outputs = run(SHIFTED, 'shifted', refuses='entry-run-incomplete')
    assert report['status'] == 'refused' and not outputs.exists()
