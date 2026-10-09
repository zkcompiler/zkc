"""A generic Sumcheck library uses closed ring assets through ordinary Entries."""
import json
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


def build(toolchain, journal, directory, entry, flags=()):
    package = directory / f'{entry}.entry'
    report = json.loads(journal.run([
        toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
        f'--module=expression_sumcheck={ROOT}/libraries/sumcheck/expression.zkc',
        f'--module=example={PROJECT}/main.zkc', f'--entry=example::{entry}',
        f'--output={package}', *flags]))
    assets = write(directory, 'assets.json', ['zkc.ring-assets/0', [
        [DIGEST, str(PROJECT / 'product.ring.json')]]])
    return package, report['package_sha256'], f'--evaluators={assets}'


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('extension', [False, True])
def test_expression_sumcheck_independent_proof(toolchain, journal, directory, flags, extension):
    package, pin, assets = build(toolchain, journal, directory, 'Proof' if extension else 'BaseProof', flags)
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0', 'public': values(extension)})
    proof = directory / 'proof.bin'
    produced = json.loads(journal.run([toolchain.runtime, 'prove', package, pin, request, proof, assets]))
    checked = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, request, proof, assets]))
    assert checked['status'] == 'accepted'
    assert produced['execution']['ring_work'] > checked['execution']['ring_work'] > 0
    truncated = directory / 'truncated.bin'
    truncated.write_bytes(proof.read_bytes()[:-1])
    journal.run([toolchain.runtime, 'verify', package, pin, request, truncated, assets], refuses='proof-truncated')
    altered = bytearray(proof.read_bytes())
    altered[-32] ^= 1  # A canonical coefficient change, preserving framing.
    changed = directory / 'changed.bin'
    changed.write_bytes(altered)
    journal.run([toolchain.runtime, 'verify', package, pin, request, changed, assets], refuses='artifact-stopped')


@pytest.mark.parametrize('extension', [False, True])
def test_expression_sumcheck_interactive_fields(toolchain, journal, directory, extension):
    entry = 'ExtensionRun' if extension else 'BaseRun'
    package, pin, assets = build(toolchain, journal, directory, entry)
    inputs = values(extension)
    request = write(directory, 'run.json', {'format': 'zkc.entry-run/0',
        'session': 'expression_sumcheck_test', 'roles': {
            'P': {'inputs': {k: v for k, v in inputs.items() if k != 'claim'}},
            'V': {'inputs': inputs}}})
    output = directory / 'output.json'
    result = json.loads(journal.run([toolchain.runtime, 'run', package, pin, request,
                                   assets, f'--results={output}']))
    assert result['status'] == 'executed'
    assert json.loads(output.read_text())['roles']['V']['accepted'] is True


@pytest.mark.parametrize('extension', [False, True])
@pytest.mark.parametrize('table,claim', [([1, 2, 3, 4, 1, 2, 3, 4], 28), ([0] * 8, 0)])
def test_expression_sumcheck_retains_zero_coefficients(toolchain, journal, directory, extension, table, claim):
    package, pin, assets = build(toolchain, journal, directory, 'Proof' if extension else 'BaseProof')
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0',
        'public': values(extension=extension, table=table, claim=claim)})
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, request, proof, assets])
    checked = json.loads(journal.run([toolchain.runtime, 'verify', package, pin, request, proof, assets]))
    assert checked['status'] == 'accepted'


@pytest.mark.parametrize('claim,rounds', [(101, 2), (100, 1), (100, 3)])
def test_expression_sumcheck_actual_claim_and_terminal_shape(toolchain, journal, directory, claim, rounds):
    package, pin, assets = build(toolchain, journal, directory, 'Proof')
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0',
                                             'public': values(claim=claim, rounds=rounds)})
    proof = directory / 'proof.bin'
    if rounds == 3:
        # A third fold cannot split the final factor row into two assignments.
        journal.run([toolchain.runtime, 'prove', package, pin, request, proof, assets], refuses='ring-input-shape')
    else:
        journal.run([toolchain.runtime, 'prove', package, pin, request, proof, assets])
        journal.run([toolchain.runtime, 'verify', package, pin, request, proof, assets], refuses='artifact-stopped')


def test_expression_asset_authority(toolchain, journal, directory):
    package, pin, assets = build(toolchain, journal, directory, 'Proof')
    request = write(directory, 'request.json', {'format': 'zkc.entry-proof/0', 'public': values()})
    proof = directory / 'proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, request, proof], refuses='ring-asset-missing')
    changed = json.loads((PROJECT / 'product.ring.json').read_text())
    changed[2][-1][0] = 'add'
    changed_path = write(directory, 'changed.ring.json', changed)
    wrong = write(directory, 'wrong-assets.json', ['zkc.ring-assets/0', [[DIGEST, str(changed_path)]]])
    journal.run([toolchain.runtime, 'prove', package, pin, request, proof,
                 f'--evaluators={wrong}'], refuses='ring-asset-identity')
    journal.run([toolchain.runtime, 'prove', package, pin, request, proof, assets])
    changed_public = values(claim=101)
    changed_request = write(directory, 'changed-request.json', {
        'format': 'zkc.entry-proof/0', 'public': changed_public})
    journal.run([toolchain.runtime, 'verify', package, pin, changed_request, proof, assets], refuses='proof-header')
