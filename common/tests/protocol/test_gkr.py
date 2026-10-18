"""The GKR library through the compiler and the Entry Host.

An independent reference evaluates uniform-width layered circuits and builds
their stacked wiring tables. Positive cases cover padded layers and gates;
negative controls cover a wrong output, a nonzero claim at a padding gate, a
prover whose intermediate layer values disagree with the statement while its
outputs agree, and a changed proof message.
"""
import json
from pathlib import Path

import pytest

from input_files import input_files

ROOT = Path(__file__).resolve().parents[3]
PROJECT = ROOT / 'examples/projects/gkr'
MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def layer_values(inputs, width, gates):
    """Gate values of every layer, output layer first. `gates[i]` lists
    (kind, gate, left, right) for layer i; unlisted gates are padding and
    evaluate to zero."""
    values = [list(inputs)]
    for layer in reversed(gates):
        below = values[0]
        current = [0] * (1 << width)
        for kind, gate, left, right in layer:
            current[gate] = ((below[left] + below[right]) if kind == 'add' else
                             below[left] * below[right]) % MODULUS
        values.insert(0, current)
    return values


def statement(inputs, width, selector, gates, padding=0):
    """Public inputs of the Entry. Blocks after the last layer hold `padding`."""
    layers = len(gates)
    assert layers <= 1 << selector and len(inputs) == 1 << width
    block = 1 << (3 * width)
    add = [padding] * (block << selector)
    mul = [padding] * (block << selector)
    for position in range(layers * block):
        add[position] = mul[position] = 0
    for layer, wiring in enumerate(gates):
        for kind, gate, left, right in wiring:
            index = layer * block + (gate << (2 * width)) + (left << width) + right
            (add if kind == 'add' else mul)[index] = 1
    outputs = layer_values(inputs, width, gates)[0]
    return {'inputs': inputs, 'outputs': outputs, 'add': add, 'mul': mul,
            'layers': layers, 'selector': selector, 'width': width}


# Two layers of two gates: (3 + 5) * (3 * 5) and (3 * 5) + (3 * 5).
TWO_LAYERS_GATES = [
    [('mul', 0, 0, 1), ('add', 1, 1, 1)],
    [('add', 0, 0, 1), ('mul', 1, 0, 1)],
]
TWO_LAYERS = statement([3, 5], 1, 1, TWO_LAYERS_GATES)
# Three layers of four gates, with padding gates in every layer and a fourth,
# unused selector block that holds nonzero data.
PADDED_GATES = [
    [('add', 0, 0, 1), ('mul', 1, 3, 3)],
    [('mul', 0, 0, 1), ('add', 1, 2, 0), ('add', 3, 1, 3)],
    [('add', 0, 0, 1), ('mul', 1, 2, 3), ('mul', 2, 1, 1)],
]
PADDED = statement([2, 7, 1, 8], 2, 2, PADDED_GATES, padding=5)
# Outputs (a + b) + a * b at both gates: inputs 3, 5 and 1, 11 give 23.
COLLIDING = [
    [('add', 0, 0, 1), ('add', 1, 0, 1)],
    [('add', 0, 0, 1), ('mul', 1, 0, 1)],
]
CIRCUITS = {'two-layers': TWO_LAYERS, 'padded': PADDED}


def build(toolchain, journal, directory, entry, flags=()):
    package = directory / f'{entry}.zkpkg'
    report = json.loads(journal.run([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--project={PROJECT}/zkc.toml', f'example::{entry}', f'--output={package}', *flags]))
    return package, report['package_sha256']


def prove(toolchain, journal, directory, package, pin, public, name='proof'):
    proof = directory / f'{name}.bin'
    producer = input_files(journal, f'{name}.producer', public=public)
    journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer,
                 f'--output={proof}'])
    return proof


def verify(toolchain, journal, package, pin, public, proof, name='verifier', refuses=None):
    verifier = input_files(journal, name, public=public)
    return json.loads(journal.run([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}',
                                   *verifier, f'--proof={proof}'], refuses=refuses))


def run(toolchain, journal, directory, package, pin, prover, verifier, name):
    inputs = input_files(journal, name, roles={'P': {'inputs': prover}, 'V': {'inputs': verifier}})
    outputs = directory / f'{name}.outputs.json'
    report = json.loads(journal.run([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}',
                                     *inputs, f'--results={outputs}']))
    assert report['status'] == 'executed'
    return json.loads(outputs.read_text())['roles']['V']['accepted']


def prover_inputs(public):
    return {name: value for name, value in public.items() if name != 'outputs'}


def test_reference_circuits():
    assert layer_values([3, 5], 1, TWO_LAYERS_GATES) == [[120, 30], [8, 15], [3, 5]]
    assert layer_values([2, 7, 1, 8], 2, PADDED_GATES)[1:3] == [[72, 58, 0, 8], [9, 8, 49, 0]]
    assert PADDED['outputs'] == [72 + 58, 8 * 8, 0, 0]
    for inputs in ([3, 5], [1, 11]):
        assert layer_values(inputs, 1, COLLIDING)[0] == [23, 23]


def test_example_inputs_are_reference_statements():
    public = json.loads((PROJECT / 'inputs/example.Proof/public.json').read_text())
    expected = {name: [str(v) for v in value] if isinstance(value, list) else str(value)
                for name, value in TWO_LAYERS.items()}
    assert public == expected
    for role in ['P', 'V']:
        values = json.loads((PROJECT / f'inputs/example.Interactive/{role}.json').read_text())
        assert values == (expected if role == 'V' else prover_inputs(expected))


@pytest.mark.parametrize('circuit', sorted(CIRCUITS))
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_gkr_accepts_circuit_outputs(toolchain, journal, directory, circuit, flags):
    public = CIRCUITS[circuit]
    package, pin = build(toolchain, journal, directory, 'Proof', flags)
    proof = prove(toolchain, journal, directory, package, pin, public)
    report = verify(toolchain, journal, package, pin, public, proof)
    assert report['status'] == 'accepted' and report['binding_scope'] == 'transcript'
    truncated = directory / 'truncated.bin'
    truncated.write_bytes(proof.read_bytes()[:-1])
    verify(toolchain, journal, package, pin, public, truncated, name='truncated', refuses='proof-truncated')
    package, pin = build(toolchain, journal, directory, 'Interactive', flags)
    assert run(toolchain, journal, directory, package, pin, prover_inputs(public), public, 'interactive') is True


@pytest.mark.parametrize('change', ['output', 'padding-output'])
def test_gkr_rejects_wrong_outputs(toolchain, journal, directory, change):
    public = json.loads(json.dumps(PADDED))
    if change == 'output':
        public['outputs'][1] = (public['outputs'][1] + 1) % MODULUS
    else:
        # The fourth output gate has no wiring, so its value is zero.
        public['outputs'][3] = 1
    package, pin = build(toolchain, journal, directory, 'Proof')
    # The honest prover follows the circuit; its first round polynomial sums to
    # the true outputs at the verifier's point.
    proof = prove(toolchain, journal, directory, package, pin, public)
    rejected = verify(toolchain, journal, package, pin, public, proof, refuses='artifact-stopped')
    assert rejected['execution']['stop']['role'] == 'role00000001'
    assert rejected['execution']['stop']['kind'] == 'Explicit("reject")'


def test_gkr_rejects_wrong_layer_values(toolchain, journal, directory):
    """The prover evaluates the circuit on other inputs with the same outputs.
    Every sumcheck and line check passes on its own layer values; the
    verifier's input evaluation at the final point rejects."""
    verifier = statement([3, 5], 1, 1, COLLIDING)
    prover = prover_inputs(statement([1, 11], 1, 1, COLLIDING))
    assert verifier['outputs'] == [23, 23]
    package, pin = build(toolchain, journal, directory, 'Interactive')
    assert run(toolchain, journal, directory, package, pin, prover_inputs(verifier), verifier, 'honest') is True
    assert run(toolchain, journal, directory, package, pin, prover, verifier, 'wrong-layers') is False


def test_gkr_rejects_changed_line_coefficient(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'Proof')
    proof = prove(toolchain, journal, directory, package, pin, TWO_LAYERS)
    changed = bytearray(proof.read_bytes())
    changed[-32] ^= 1  # The last line coefficient, with its framing intact.
    proof.write_bytes(changed)
    verify(toolchain, journal, package, pin, TWO_LAYERS, proof, name='changed', refuses='artifact-stopped')
