"""The native hash-chain transcript suites.

The reference in `hash_chain_reference.py` implements Keccak-f[1600] and the
chain independently of native code; the backend vector fixture is checked
against it here and against the native kernels by the Rust backend tests. The
maintained Schnorr, Sumcheck and FRI examples then prove and verify under the
suites. These runs check execution, binding and refusal; they establish no
security property of the suite.
"""
import hashlib
import json
from pathlib import Path

import pytest

import hash_chain_reference as reference
from input_files import input_files
from octic_reference import P, ZERO, add, mul
from project import project_inputs

ROOT = Path(__file__).resolve().parents[3]
VECTORS = ROOT / 'crates/zkc-test-support/fixtures/hash-chain-vectors.json'
MERLIN = 'merlin3.bls12-381.fr64be/0'
MERLIN_OCTIC = 'merlin3.koala-bear.ext8-binomial3.rejection31le/0'
CHAIN = 'hash-chain.keccak256.bls12-381.fr64be/0'
CHAIN_OCTIC = 'hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0'
CHAIN_QUARTIC = 'hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0'


def test_reference_keccak_reproduces_published_answers_and_the_sha3_permutation():
    # Keccak-256 of the empty string and of "abc", as published with the
    # Keccak submission and used by Ethereum.
    assert reference.keccak256(b'').hex() == (
        'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')
    assert reference.keccak256(b'abc').hex() == (
        '4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45')
    # SHA3-256 shares the permutation and rate; only the padding differs.
    for length in [0, 1, 135, 136, 137, 271, 272, 273, 1000]:
        data = bytes((7 * i + length) % 256 for i in range(length))
        assert reference.sha3_256(data) == hashlib.sha3_256(data).digest()
        assert reference.keccak256(data) != reference.sha3_256(data)


def test_backend_vector_fixture_is_the_reference_output():
    assert VECTORS.read_text() == reference.render(reference.vectors())


def test_quartic_backend_vector_is_the_independent_reference_output():
    vector = reference.vectors([(reference.QUARTIC_SUITE,
                                'random.koala-bear.ext4-binomial3/0',
                                reference.QUARTIC_SEVEN, 4)])['suites'][0]
    assert vector == json.loads((ROOT / 'crates/zkc-cpu/tests/common/quartic-hash-chain.json').read_text())


def test_chain_inputs_parse_uniquely():
    root = b'\x01' + bytes(8)
    chain = reference.Chain(CHAIN, root)
    chain.absorb(b'origin', b'a')
    chain.request(b'challenge', 64)
    chain.absorb(b'value', b'')
    tags = {reference.BIND_TAG, reference.ABSORB_TAG, reference.REQUEST_TAG}
    # No role tag is a prefix of another, so the role of every primitive input
    # is its leading tag.
    assert all(not b.startswith(a) for a in tags for b in tags if a != b)
    inputs = [data for data, _ in chain.calls]
    assert len(set(inputs)) == len(inputs)
    # Frames carry their lengths: moving a byte between label and data, or
    # between data and the next frame, changes the input.
    assert reference.frame(1, b'ab', b'c') != reference.frame(1, b'a', b'bc')
    assert (reference.frame(1, b'v', b'x') + reference.frame(1, b'v', b'')
            != reference.frame(1, b'v', b'') + reference.frame(1, b'v', b'x'))
    # A request is not a message with the same label and data.
    assert (reference.frame(reference.REQUEST, b'challenge', (64).to_bytes(8, 'big'))
            != reference.frame(reference.MESSAGE, b'challenge', (64).to_bytes(8, 'big')))
    # The suite name is bound at initialization, so two instances never share a state.
    assert reference.Chain(CHAIN, root).state != reference.Chain(CHAIN_OCTIC, root).state


def substitute(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


def compile_project(toolchain, journal, directory, project, entry, suite=None, old=MERLIN):
    """Compile a maintained example, optionally with its suite replaced."""
    modules, assets = project_inputs(ROOT / project / 'zkc.toml')
    if suite is not None:
        source = directory / f'{Path(project).name}-{entry}.zkc'
        source.write_text(substitute(modules['example'].read_text(),
                                     f'fiat_shamir("{old}"', f'fiat_shamir("{suite}"'))
        modules['example'] = source
    package = directory / f'{Path(project).name}-{entry}-{suite is not None}.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                           *[f'--module={name}={path}' for name, path in sorted(modules.items())],
                           *[f'--asset={name}={kind}={path}' for name, (kind, path) in sorted(assets.items())],
                           f'example::{entry}', f'--output={package}'])
    return [f'--package={package}', f'--sha256={report["package_sha256"]}']


def read(project, group):
    path = ROOT / project / f'inputs/example.Proof/{group}.json'
    return json.loads(path.read_text()) if path.exists() else {}


def prove_and_verify(toolchain, journal, directory, target, producer, verifier):
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *target, *producer,
                             f'--output={proof}'])
    assert produced['status'] == 'produced'
    accepted = journal.json([toolchain.runtime, '--json', 'verify', *target, *verifier,
                             f'--proof={proof}'])
    assert accepted['status'] == 'accepted' and accepted['binding_scope'] == 'transcript'
    return proof


@pytest.mark.parametrize('project', ['examples/projects/schnorr', 'examples/projects/sumcheck'])
def test_bls_examples_prove_and_verify_under_the_hash_chain(toolchain, journal, directory, project):
    target = compile_project(toolchain, journal, directory, project, 'Proof', CHAIN)
    public, witness = read(project, 'public'), read(project, 'witness')
    producer = input_files(journal, 'producer', public=public, witness=witness)
    verifier = input_files(journal, 'verifier', public=public)
    proof = prove_and_verify(toolchain, journal, directory, target, producer, verifier)
    honest = proof.read_bytes()
    # The final frame is the last prover message, read after the last
    # challenge: changing it changes what V checks.
    changed = bytearray(honest)
    changed[-1] ^= 1
    proof.write_bytes(changed)
    journal.run([toolchain.runtime, '--json', 'verify', *target, *verifier, f'--proof={proof}'],
                refuses='artifact-rejected' if 'schnorr' in project else 'artifact-stopped')
    # The Merlin compilation of the same source has a different policy, so
    # its binding root differs and it refuses this proof at the header.
    proof.write_bytes(honest)
    merlin = compile_project(toolchain, journal, directory, project, 'Proof')
    journal.run([toolchain.runtime, '--json', 'verify', *merlin, *verifier, f'--proof={proof}'],
                refuses='proof-header')


SHIFT = [3, 1, 0, 0, 0, 0, 0, 0]


def octic_word(coefficients, log_size):
    """Evaluations on the shifted subgroup of size 2^log_size, as the FRI test builds them."""
    size = 1 << log_size
    root = pow(1791270792, (1 << 24) // size, P)

    def evaluate(point):
        result = ZERO
        for coefficient in reversed(coefficients):
            result = add(coefficient, mul(point, result))
        return result
    return [evaluate(mul(SHIFT, [pow(root, i, P)] + [0] * 7)) for i in range(size)]


def test_fri_example_proves_and_verifies_under_the_octic_hash_chain(toolchain, journal, directory):
    project = 'examples/projects/fri'
    target = compile_project(toolchain, journal, directory, project, 'Proof', CHAIN_OCTIC,
                             old=MERLIN_OCTIC)
    public = {'shift': [str(c) for c in SHIFT], 'round_count': 3, 'query_count': 8}
    word = octic_word([[i + 1, i * i, 0, 0, 0, 0, 0, 1] for i in range(8)], 5)
    producer = input_files(journal, 'producer', public=public,
                           witness={'word': [[str(c) for c in v] for v in word]})
    verifier = input_files(journal, 'verifier', public=public)
    proof = prove_and_verify(toolchain, journal, directory, target, producer, verifier)
    # A changed first root moves every drawn position and fold challenge.
    changed = bytearray(proof.read_bytes())
    changed[40 + 8 + 10] ^= 1
    proof.write_bytes(changed)
    journal.run([toolchain.runtime, '--json', 'verify', *target, *verifier, f'--proof={proof}'],
                refuses='artifact-stopped')


SOURCE = '''module sample;
domain F = field("FIELD");
fn agree(a: F, b: F) -> bool { return a == b; }
// P returns the derived challenge, so V compares it with its own sample.
protocol Echo roles(P,V)(coins: Random<F> @V) -> (ok: bool @V) {
  let c = coins.draw();
  let d = send V -> P(c);
  let e = send P -> V(d);
  let ok @V = agree(c, e);
  return (ok = ok);
}
proof Demo = Echo { prover P; verifier V; public {}; accept ok;
  construction fiat_shamir("SUITE", coins); }
'''


DIFFERENT_FIELD = 'construction field differs from service'
NOT_INSTALLED = 'construction requires an installed suite and matching verifier service'


@pytest.mark.parametrize('field,suite,reason', [
    # The suite's challenge field must be the replaced service's field.
    ('koala-bear.ext8-binomial3', CHAIN, DIFFERENT_FIELD),
    ('bls12-381.fr', CHAIN_OCTIC, DIFFERENT_FIELD),
    # Another byte hash is a separate installation, not a parameter.
    ('bls12-381.fr', 'hash-chain.sha256.bls12-381.fr64be/0', NOT_INSTALLED),
    ('koala-bear.ext4-binomial3', CHAIN_OCTIC, DIFFERENT_FIELD),
])
def test_unsupported_suite_selections_refuse(toolchain, journal, directory, field, suite, reason):
    source = directory / 'main.zkc'
    source.write_text(SOURCE.replace('FIELD', field).replace('SUITE', suite))
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=sample={source}', 'sample::Demo',
                           f'--output={directory / "p.zkpkg"}'], refuses='source-compilation')
    assert reason in report['diagnostics']


@pytest.mark.parametrize('field,suite', [('bls12-381.fr', CHAIN),
                                         ('koala-bear.ext4-binomial3', CHAIN_QUARTIC),
                                         ('koala-bear.ext8-binomial3', CHAIN_OCTIC)])
def test_echoed_challenges_match_and_a_changed_echo_is_rejected(toolchain, journal, directory, field, suite):
    source = directory / 'main.zkc'
    source.write_text(SOURCE.replace('FIELD', field).replace('SUITE', suite))
    package = directory / 'p.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=sample={source}', 'sample::Demo', f'--output={package}'])
    target = [f'--package={package}', f'--sha256={report["package_sha256"]}']
    proof = prove_and_verify(toolchain, journal, directory, target, [], [])
    changed = bytearray(proof.read_bytes())
    changed[-1] ^= 1
    proof.write_bytes(changed)
    journal.run([toolchain.runtime, '--json', 'verify', *target, f'--proof={proof}'],
                refuses='artifact-rejected')
