"""A maintained source client samples verifier positions through managed services.

The spot check commits P's rows, samples UniformIndex(8) at V, and checks the
authenticated opening at that position. The proof Entry derives each position
from the native transcript; the run Entry draws it from V's managed service.
"""
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CLIENT = ROOT / 'compiler/test/fixtures/language/index_sampling.zkc'
ROWS = [[i + 1, 2 * i, 0, 0, 0, 0, 0, 7] for i in range(8)]
SHIFTED = [[i + 2, 2 * i, 0, 0, 0, 0, 0, 7] for i in range(8)]


def vector(rows):
    """A canonical octic-extension vector frame."""
    return (b'ZKCV\x00\x1b' + len(rows).to_bytes(4, 'little')
            + b''.join(x.to_bytes(4, 'little') for row in rows for x in row)).hex()


def compile_entry(toolchain, journal, directory, entry, flags=()):
    package = directory / f'{entry}.entry'
    report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=sample={CLIENT}', f'--entry=sample::{entry}',
                           f'--output={package}', *flags])
    assert report['status'] == 'compiled'
    return package, report['package_sha256']


def write(path, value):
    path.write_text(json.dumps(value))
    return path


def write_bytes(path, value):
    path.write_bytes(bytes(value))
    return path


def requests(directory, rows=ROWS, rounds=3, name='honest'):
    public = {'expected': vector(ROWS), 'rounds': rounds}
    producer = write(directory / f'{name}.producer.json',
                     {'format': 'zkc.entry-proof/0', 'public': public, 'inputs': {'values': vector(rows)}})
    verifier = write(directory / f'{name}.verifier.json',
                     {'format': 'zkc.entry-proof/0', 'public': public, 'inputs': {}})
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
    producer, verifier = requests(directory)
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, 'prove', package, pin, producer, proof])
    assert produced['status'] == 'produced'
    # Five ordered transitions per round: root, index, delivery, row and path.
    transcript = [r for r in produced['execution']['resources'] if r['stage'] == 'transcript']
    assert transcript[0]['transitions'] == 15
    accepted = journal.json([toolchain.runtime, 'verify', package, pin, verifier, proof])
    assert accepted['status'] == 'accepted' and accepted['binding_scope'] == 'transcript'
    # Root, row and path per round; the sampled positions are never sent.
    assert len(frames(proof.read_bytes())) == 9


def test_altered_rows_proofs_and_statements_are_refused(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Proof')
    producer, verifier = requests(directory)
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    original = proof.read_bytes()

    # Every committed row differs from V's copy, so every sampled position fails.
    shifted, _ = requests(directory, SHIFTED, name='shifted')
    wrong = directory / 'wrong.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, shifted, wrong])
    journal.run([toolchain.runtime, 'verify', package, pin, verifier, wrong], refuses='artifact-stopped')

    # Change one coordinate of the first opened row, keeping it canonical.
    offset, payload = frames(original)[1]
    assert payload[:6] == b'ZKCV\x00\x1b'
    changed = bytearray(original)
    changed[offset + 10] ^= 1
    altered = write_bytes(directory / 'altered.bin', changed)
    journal.run([toolchain.runtime, 'verify', package, pin, verifier, altered], refuses='artifact-stopped')
    truncated = write_bytes(directory / 'truncated.bin', original[:-1])
    journal.run([toolchain.runtime, 'verify', package, pin, verifier, truncated], refuses='proof-truncated')

    # The public statement seeds the transcript; another round count is refused.
    _, other = requests(directory, rounds=2, name='fewer')
    journal.run([toolchain.runtime, 'verify', package, pin, other, proof], refuses='proof-header')


def test_managed_service_positions_run(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, 'Interactive')
    def run(rows, name, refuses=None):
        request = write(directory / f'{name}.json', {
            'format': 'zkc.entry-run/0', 'session': 'index_sampling',
            'roles': {'P': {'inputs': {'values': vector(rows), 'rounds': 3}},
                      'V': {'inputs': {'expected': vector(ROWS), 'rounds': 3}}}})
        outputs = directory / f'{name}.outputs.json'
        report = journal.json([toolchain.runtime, 'run', package, pin, request,
                               f'--results={outputs}'], refuses=refuses)
        return report, outputs
    report, outputs = run(ROWS, 'honest')
    assert report['status'] == 'executed'
    assert json.loads(outputs.read_text())['roles']['V']['accepted'] is True
    report, outputs = run(SHIFTED, 'shifted', refuses='entry-run-incomplete')
    assert report['status'] == 'refused' and not outputs.exists()
