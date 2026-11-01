"""Compiled block requests, construction witnesses and independent byte replay.

This echo client tests the construction/transport boundary, not a soundness
claim. The reference implements Keccak in Python and never calls the provider.
"""
import hashlib
import json
from pathlib import Path

import pytest

from hash_chain_reference import Chain
from logical_tree import decode_tree, encode_tree


SUITE = 'hash-chain.keccak256.koala-bear.extDEGREE-binomial3.rejection31le/0'
SOURCE = '''module { "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%secret: ui64, %coins: !protocol.service_ref<"random.koala-bear.extDEGREE-binomial3/0">):
    %first = protocol.exchange %secret {site="commitment", sender="P", receiver="V"} : ui64
    %n = "data.index"() {value=16 : ui64} : () -> ui64
    %q = "data.index"() {value=4 : ui64} : () -> ui64
    %sample = "protocol.query"(%coins, %n, %q) {method="indices", owner="V", site="pick"} : (!protocol.service_ref<"random.koala-bear.extDEGREE-binomial3/0">, ui64, ui64) -> !data.indices
    %actual = protocol.exchange %sample {site="delivery", sender="V", receiver="P"} : !data.indices
    %echo = protocol.exchange %actual {site="response", sender="P", receiver="V"} : !data.indices
    %ok = arith.constant true
    "protocol.return"(%ok) : (i1) -> ()
  }) {sym_name="main", function_type=(ui64, !protocol.service_ref<"random.koala-bear.extDEGREE-binomial3/0">) -> i1,
      roles=["P","V"], input_roles=[["P"],["V"]], output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
'''


def origin(template):
    tree = decode_tree(bytes.fromhex(template))
    assert tree[0] == 'zkc.native-origin-template/0'
    tree[0] = 'zkc.native-origin/0'
    return encode_tree(tree)


def replay(deployment, proof, secret, difficulty):
    descriptor = deployment[2]
    binding = encode_tree(['zkc.native-proof-binding/0', 'sha256', 'zkc.native-origin/0',
                          deployment[1], 'main', 'P', 'V', descriptor, [], ''])
    assert proof[:8] == b'ZKCPRF00'
    assert proof[8:40] == hashlib.sha256(binding).digest()
    chain = Chain(descriptor[1][5], binding)
    position = 40
    spans = []

    def receive():
        nonlocal position
        size = int.from_bytes(proof[position:position + 8], 'little')
        position += 8
        start = position
        position += size
        assert position <= len(proof)
        spans.append((start, position))
        return proof[start:position]

    def observe(event, wire):
        chain.absorb(b'origin', origin(event[1]))
        chain.absorb(b'value', wire)

    events = descriptor[3]
    assert len(events) == 4
    assert events[0][0] == events[2][0] == events[3][0] == 'message'
    commit = receive()
    assert commit == b'ZKCV\x00\x1f' + secret.to_bytes(8, 'little')
    observe(events[0], commit)
    request = events[1]
    gated = difficulty is not None
    assert request[0] == ('gated-indices' if gated else 'indices')
    assert request[2:4] == ['16', '4']
    if gated:
        assert request[4] == str(difficulty)
        assert descriptor[7] == [[request[1], 'gate.pick', 'index', 'native.index/0']]
        wire = receive()
        assert len(wire) == 14 and wire[:6] == b'ZKCV\x00\x1f'
        witness = int.from_bytes(wire[6:], 'little')
    else:
        assert descriptor[7] == []
        witness = None
    chain.absorb(b'origin', origin(request[1]))
    chain.absorb(b'bound', (16).to_bytes(8, 'little'))
    chain.absorb(b'count', (4).to_bytes(8, 'little'))
    if difficulty:
        chain.absorb(b'difficulty', difficulty.to_bytes(8, 'little'))
        chain.absorb(b'gate-witness', wire)
        raw = chain.request(b'gated-indices', 40)
        assert int.from_bytes(raw[:8], 'little') & ((1 << difficulty) - 1) == 0
        raw = raw[8:]
    else:
        assert witness in (None, 0)
        raw = chain.request(b'indices', 32)
    values = [int.from_bytes(raw[i:i + 8], 'little') & 15 for i in range(0, 32, 8)]
    # Native indices: exact tag and u32 count, then Q little-endian u64s.
    echo = receive()
    assert len(echo) == 42 and echo[:6] == b'ZKCV\x00D'
    assert int.from_bytes(echo[6:10], 'little') == 4
    assert [int.from_bytes(echo[i:i + 8], 'little') for i in range(10, 42, 8)] == values
    observe(events[2], echo)
    observe(events[3], echo)
    assert position == len(proof)
    return spans


@pytest.mark.parametrize('degree', [4, 8])
@pytest.mark.parametrize('difficulty', [None, 0, 6])
@pytest.mark.parametrize('flags', [[], ['--no-simplify', '--release-storage']])
def test_compiled_native_index_blocks(toolchain, journal, directory, degree, difficulty, flags):
    source = directory / 'source.mlir'
    source.write_text(SOURCE.replace('DEGREE', str(degree)))
    suite = SUITE.replace('DEGREE', str(degree))
    gates = [] if difficulty is None else [['pick', str(difficulty)]]
    policy = journal.write('policy.json', ['zkc.native-proof-policy/0', 'main', 'P', 'V',
                           '0', suite, ['1'], [], [['pick', 'delivery']], 'zkc.framed/0', '', gates])
    deployment = journal.json([toolchain.compiler, 'protocol-proof', source, policy, *flags])
    artifact = journal.write('deployment.json', deployment)
    pin = hashlib.sha256(artifact.read_bytes()).hexdigest()
    secret = 37
    producer = journal.write('producer.json', ['zkc.native-proof-inputs/0', [],
                             [['0', ['wire', (b'ZKCV\x00\x1f' + secret.to_bytes(8, 'little')).hex()]]],
                             '', [], '4'])
    validator = journal.write('validator.json', ['zkc.native-proof-inputs/0', [], [], '', [], '4'])
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'bundle', 'prove', artifact, pin, producer, proof])
    assert produced['status'] == 'produced'
    assert journal.json([toolchain.runtime, '--json', 'bundle', 'verify', artifact, pin, validator, proof])['status'] == 'accepted'
    original = proof.read_bytes()
    spans = replay(deployment, original, secret, difficulty)
    # Search, selection and final publication are deterministic under this root.
    another = directory / 'another.bin'
    journal.json([toolchain.runtime, '--json', 'bundle', 'prove', artifact, pin, producer, another])
    assert another.read_bytes() == original
    if difficulty is not None:
        start, end = spans[1]
        changed = bytearray(original)
        changed[start + 6:end] = ((1 << 64) - 1).to_bytes(8, 'little')
        invalid = directory / 'changed-witness.bin'
        invalid.write_bytes(changed)
        # For the positive gate, deterministically find a nonce that fails the
        # reference predicate rather than assuming a random mutation rejects.
        if difficulty:
            changed[start + 6:end] = _rejected_witness(deployment, secret, difficulty).to_bytes(8, 'little')
            invalid.write_bytes(changed)
        report = journal.json([toolchain.runtime, '--json', 'bundle', 'verify', artifact, pin,
                               validator, invalid], refuses='rejected:require' if difficulty else 'refused:gate-witness')
        assert not report['cleanup_errors']
    for name, candidate, reason in [('truncated', original[:-1], 'proof-truncated'),
                                     ('trailing', original + b'\x00', 'proof-trailing')]:
        path = directory / f'{name}.bin'
        path.write_bytes(candidate)
        journal.json([toolchain.runtime, '--json', 'bundle', 'verify', artifact, pin, validator, path], refuses=reason)


def _rejected_witness(deployment, secret, bits):
    descriptor = deployment[2]
    binding = encode_tree(['zkc.native-proof-binding/0', 'sha256', 'zkc.native-origin/0',
                          deployment[1], 'main', 'P', 'V', descriptor, [], ''])
    for witness in range(1024):
        chain = Chain(descriptor[1][5], binding)
        chain.absorb(b'origin', origin(descriptor[3][0][1]))
        chain.absorb(b'value', b'ZKCV\x00\x1f' + secret.to_bytes(8, 'little'))
        chain.absorb(b'origin', origin(descriptor[3][1][1]))
        for label, value in [(b'bound', 16), (b'count', 4), (b'difficulty', bits)]:
            chain.absorb(label, value.to_bytes(8, 'little'))
        chain.absorb(b'gate-witness', b'ZKCV\x00\x1f' + witness.to_bytes(8, 'little'))
        if int.from_bytes(chain.request(b'gated-indices', 40)[:8], 'little') & ((1 << bits) - 1):
            return witness
    raise AssertionError('no rejecting control')


@pytest.mark.parametrize('field', ['koala-bear.ext4-binomial3', 'koala-bear.ext8-binomial3',
                                  'baby-bear.ext4-binomial11', 'goldilocks.ext2-binomial7'])
def test_source_block_service_runs_through_entry_host(toolchain, journal, directory, field):
    from input_files import input_files
    from source_modules import library_modules

    source = directory / 'blocks.zkc'
    source.write_text('''module sample;
use zkc::indices::{Indices};
domain E = field("FIELD");
protocol Blocks roles(P,V)(coins: Random<E> @V) -> (positions: Indices @P) {
  let positions = coins.indices(1,7);
  let delivered = send V -> P(positions);
  return (positions = delivered);
}
'''.replace('FIELD', field))
    package = directory / 'blocks.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile',
                             f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                             *library_modules('core/collections'),
                             'sample::Blocks', f'--output={package}'])
    request = input_files(journal, 'run.json', session='block-service', package=package,
                          arguments={'inputs': {'P': {}, 'V': {}}})
    outputs = directory / 'outputs.json'
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={compiled["package_sha256"]}', *request,
                           f'--results={outputs}'])
    assert report['status'] == 'executed'
    assert json.loads(outputs.read_text())['value']['P']['positions'] == ['0'] * 7


@pytest.mark.parametrize('all_gated', [False, True])
def test_applied_source_blocks_keep_distinct_witness_slots(toolchain, journal, directory, all_gated):
    fixture = Path(__file__).resolve().parents[3] / 'compiler/test/fixtures/language/index_block.zkc'
    source = directory / 'applied.zkc'
    source.write_text(fixture.read_text().replace(
        '    let delivered', '    let checkpoint @P = yes();\n    let delivered').replace(
        'protocol Blocks', 'protocol Child').replace(
        'proof Proof', '''
protocol Blocks<N: nat, Q: nat> roles(V,P)(rounds: index @(P,V), coins: Random<E> @V)
    -> (accepted: bool @V) {
  let first = Child<N,Q> roles(P,V)(rounds, coins);
  let second = Child<N,Q> roles(P,V)(rounds, coins);
  return (accepted = second);
}
proof Proof'''))
    selection = ['--source-format=zkc', '--entry=sample::Proof', f'--module=sample={source}']
    base = journal.json([toolchain.compiler, 'language-bundle', *selection])
    original = directory / 'source.mlir'
    original.write_text(journal.run([toolchain.compiler, 'language-emit', *selection]))
    policy = base[2][1]
    assert len(policy[8]) == 2
    selected = policy[8] if all_gated else policy[8][:1]
    policy[11] = [[site, '6'] for site, _ in selected]
    policy_file = journal.write('policy.json', policy)
    deployment = journal.json([toolchain.compiler, 'protocol-proof', original, policy_file])
    witnesses = deployment[2][7]
    assert len(witnesses) == len(selected)
    assert [row[1] for row in witnesses] == ['gate.' + site for site, _ in selected]
    assert len({row[0] for row in witnesses}) == len(witnesses)
    artifact = journal.write('deployment.json', deployment)
    pin = hashlib.sha256(artifact.read_bytes()).hexdigest()
    wire = (b'ZKCV\x00\x1f' + (2).to_bytes(8, 'little')).hex()
    inputs = journal.write('inputs.json', ['zkc.native-proof-inputs/0',
                           [[policy[3], '0', wire]], [['0', ['wire', wire]]], '', [], '24'])
    proof = directory / 'proof.bin'
    assert journal.json([toolchain.runtime, '--json', 'bundle', 'prove', artifact,
                         pin, inputs, proof])['status'] == 'produced'
    assert journal.json([toolchain.runtime, '--json', 'bundle', 'verify', artifact,
                         pin, inputs, proof])['status'] == 'accepted'
    # The descriptor cannot drop a construction slot while retaining its code.
    deployment[2][7].pop()
    changed = journal.write('missing-slot.json', deployment)
    changed_pin = hashlib.sha256(changed.read_bytes()).hexdigest()
    journal.run([toolchain.runtime, '--json', 'bundle', 'verify', changed, changed_pin,
                 inputs, proof], refuses='native-proof-descriptor-binding')
