"""A generic Sumcheck library uses closed ring assets through ordinary Entries."""
import json
from hashlib import sha256
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / 'examples/projects/expression-sumcheck'
DIGEST = '1b02fe175b0c9abcfdb134e2b9f4fa52bdfa6714fd77dd8099067394b39360d4'


def write(directory, name, value):
    path = directory / name
    path.write_text(json.dumps(value))
    return path


def values(extension=True, claim=100, rounds=2, table=tuple(range(1, 9))):
    # Independent wire construction, with four row-major assignments to x*y.
    def scalar(n):
        return n.to_bytes(4, 'little') + (bytes(28) if extension else b'')
    vector = (b'ZKCV\0' + bytes([27 if extension else 20])
              + len(table).to_bytes(4, 'little') + b''.join(scalar(n) for n in table))
    field = b'ZKCV\0' + bytes([26 if extension else 19]) + scalar(claim)
    return {'values': vector.hex(), 'claim': field.hex(), 'rounds': rounds}


def build(toolchain, journal, directory, entry, flags=(), arena=None):
    arena = arena or PROJECT / 'product.ring.json'
    package = directory / f'{entry}.zkpkg'
    modules = ([f'--project={PROJECT}/zkc.toml'] if arena == PROJECT / 'product.ring.json' else [
        f'--module=expression_sumcheck={ROOT}/libraries/sumcheck/expression.zkc',
        f'--module=zkc::vector={ROOT}/libraries/zkc/vector.zkc',
        f'--module=zkc::polynomial={ROOT}/libraries/zkc/polynomial.zkc',
        f'--module=example={PROJECT}/main.zkc', f'--asset=product=ring-json={arena}'])
    report = json.loads(journal.run([
        toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}', *modules,
        f'example::{entry}', f'--output={package}', *flags]))
    return package, report['package_sha256']


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('extension', [False, True])
def test_expression_sumcheck_independent_proof(toolchain, journal, directory, flags, extension):
    package, pin = build(toolchain, journal, directory, 'Proof' if extension else 'BaseProof', flags)
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0', 'public': values(extension)})
    proof = directory / 'proof.bin'
    produced = json.loads(journal.run([toolchain.runtime, 'prove', package, pin, request, proof]))
    checked = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, request, proof]))
    assert checked['status'] == 'accepted'
    assert produced['execution']['ring_work'] > checked['execution']['ring_work'] > 0
    truncated = directory / 'truncated.bin'
    truncated.write_bytes(proof.read_bytes()[:-1])
    journal.run([toolchain.runtime, 'verify', package, pin, request, truncated], refuses='proof-truncated')
    altered = bytearray(proof.read_bytes())
    altered[-32] ^= 1  # A canonical coefficient change, preserving framing.
    changed = directory / 'changed.bin'
    changed.write_bytes(altered)
    journal.run([toolchain.runtime, 'verify', package, pin, request, changed], refuses='artifact-stopped')


@pytest.mark.parametrize('extension', [False, True])
def test_expression_sumcheck_interactive_fields(toolchain, journal, directory, extension):
    entry = 'ExtensionRun' if extension else 'BaseRun'
    package, pin = build(toolchain, journal, directory, entry)
    inputs = values(extension)
    request = write(directory, 'run.json', {'format': 'zkc.entry-run/0',
        'session': 'expression_sumcheck_test', 'roles': {
            'P': {'inputs': {k: v for k, v in inputs.items() if k != 'claim'}},
            'V': {'inputs': inputs}}})
    output = directory / 'output.json'
    result = json.loads(journal.run([toolchain.runtime, 'run', package, pin, request,
                                   f'--results={output}']))
    assert result['status'] == 'executed'
    assert json.loads(output.read_text())['roles']['V']['accepted'] is True


@pytest.mark.parametrize('extension', [False, True])
@pytest.mark.parametrize('table,claim', [([1, 2, 3, 4, 1, 2, 3, 4], 28), ([0] * 8, 0)])
def test_expression_sumcheck_retains_zero_coefficients(toolchain, journal, directory, extension, table, claim):
    package, pin = build(toolchain, journal, directory, 'Proof' if extension else 'BaseProof')
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0',
        'public': values(extension=extension, table=table, claim=claim)})
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, request, proof])
    checked = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, request, proof]))
    assert checked['status'] == 'accepted'


@pytest.mark.parametrize('claim,rounds', [(101, 2), (100, 1), (100, 3)])
def test_expression_sumcheck_actual_claim_and_terminal_shape(toolchain, journal, directory, claim, rounds):
    package, pin = build(toolchain, journal, directory, 'Proof')
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0',
                                             'public': values(claim=claim, rounds=rounds)})
    proof = directory / 'proof.bin'
    if rounds == 3:
        # A third fold cannot split the final factor row into two assignments.
        journal.run([toolchain.runtime, 'prove', package, pin, request, proof], refuses='ring-input-shape')
    else:
        journal.run([toolchain.runtime, 'prove', package, pin, request, proof])
        journal.run([toolchain.runtime, 'verify', package, pin, request, proof], refuses='artifact-stopped')


def test_expression_asset_authority(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'Proof')
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0', 'public': values()})
    proof = directory / 'proof.bin'
    frame = json.loads(package.read_text())
    assert len(frame['assets']) == 1 and frame['assets'][0][0] == DIGEST
    assert json.loads(frame['assets'][0][1]) == json.loads((PROJECT / 'product.ring.json').read_text())
    journal.run([toolchain.runtime, 'prove', package, pin, request, proof])
    changed_public = values(claim=101)
    changed_request = write(directory, 'changed-request.json', {
        'format': 'zkc.entry-proof/0', 'public': changed_public})
    journal.run([toolchain.runtime, 'verify', package, pin, changed_request, proof], refuses='proof-header')



def test_expression_package_asset_refusals(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'Proof')
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0', 'public': values()})
    for name in ['missing', 'substitution', 'noncanonical', 'duplicate', 'field-absent']:
        frame = json.loads(package.read_text())
        reason = 'entry-package-format'
        if name == 'missing':
            frame['assets'] = []
            reason = 'entry-asset-missing'
        elif name == 'substitution':
            arena = json.loads(frame['assets'][0][1])
            arena[2][-1][0] = 'add'
            frame['assets'][0][1] = json.dumps(arena, separators=(',', ':'))
            reason = 'ring-asset-identity'
        elif name == 'noncanonical':
            frame['assets'][0][1] += '\n'
            reason = 'entry-asset-canonical'
        elif name == 'duplicate':
            frame['assets'] *= 2
        else:
            del frame['assets']
        path = write(directory, f'{name}.zkpkg', frame)
        changed_pin = sha256(path.read_bytes()).hexdigest()
        proof = directory / f'{name}.proof'
        journal.run([toolchain.runtime, 'prove', path, changed_pin, request, proof], refuses=reason)
        assert not proof.exists()
        journal.run([toolchain.runtime, 'prove', path, pin, request, proof],
                    refuses='entry-package-identity')


def test_expression_dimensions_and_degree_follow_captured_contents(toolchain, journal, directory):
    # The same source component evaluates x*y*z. Its width and cubic round bound
    # come from the captured arena without editing either client or library.
    arena = ['zkc.ring/0', ['koala-bear'] * 3,
             [['input', 0], ['input', 1], ['input', 2], ['mul', 0, 1], ['mul', 3, 2]], [4]]
    arena_path = write(directory, 'cubic.ring.json', arena)
    package, pin = build(toolchain, journal, directory, 'Proof', arena=arena_path)
    table = tuple(range(1, 13))
    claim = sum(table[i] * table[i + 1] * table[i + 2] for i in range(0, 12, 3))
    request = write(directory, 'cubic-request.json', {'format': 'zkc.entry-proof/0',
        'public': values(table=table, claim=claim)})
    proof = directory / 'cubic.proof'
    journal.run([toolchain.runtime, 'prove', package, pin, request, proof])
    result = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, request, proof]))
    assert result['status'] == 'accepted'


def test_compiler_asset_sharing_reduces_work_without_changing_sumcheck(toolchain, journal, directory):
    arena = ['zkc.ring/0', ['koala-bear'] * 2,
             [['input', 0], ['input', 1], ['mul', 0, 1],
              ['input', 0], ['input', 1], ['mul', 3, 4], ['add', 2, 5]], [6]]
    authored = write(directory, 'repeated.ring.json', arena)
    shared = directory / 'shared.ring.json'
    shared.write_text(journal.run([toolchain.compiler, 'asset-share', 'ring-json', authored]))
    rewritten = json.loads(shared.read_text())
    assert rewritten[1] == arena[1] and len(rewritten[2]) == 4 < len(arena[2])
    request = write(directory, 'sharing-request.json', {'format': 'zkc.entry-proof/0',
        'public': values(claim=200)})
    results = []
    identities = []
    for name, path in [('authored', authored), ('shared', shared)]:
        package, pin = build(toolchain, journal, directory, 'Proof', arena=path)
        identities.append(json.loads(package.read_text())['assets'][0][0])
        proof = directory / f'{name}.proof'
        produced = json.loads(journal.run([toolchain.runtime, 'prove', package, pin, request, proof]))
        verified = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, request, proof]))
        assert verified['status'] == 'accepted'
        results.append((produced['execution']['ring_work'], verified['execution']['ring_work']))
    assert identities[0] != identities[1]
    assert results[1][0] < results[0][0] and results[1][1] < results[0][1]


def test_asset_sharing_command_refusals(toolchain, journal):
    journal.run([toolchain.compiler, 'asset-share'], refuses='asset-sharing-command')
    journal.run([toolchain.compiler, 'asset-share', 'unknown', '/not/opened'],
                refuses='asset-sharing-kind')
