"""C++ and Rust independently decode exact arenas and reject shared mutations."""
from copy import deepcopy
from hashlib import sha256
import json
import random


def test_ring_admission_and_identity_agree(toolchain, journal):
    field = 'koala-bear'
    ext = 'koala-bear.ext8-binomial3'
    cases = []

    def add(value, admitted=True):
        cases.append((json.dumps(value, separators=(',', ':')), admitted))

    add(['zkc.ring/0', [], [], []])
    add(['zkc.ring/0', [field], [], []])  # A vacuous view can declare unused inputs.
    arena = ['zkc.ring/0', [field, field], [['input', 0], ['input', 1], ['mul', 0, 1]], [2]]
    add(arena)
    add(['zkc.ring/0', [field], [['input', 0], ['embed', ext, 0]], [1]])
    for prime, modulus in [('koala-bear', 2130706433),
            ('koala-bear.ext8-binomial3', 2130706433),
            ('bn254.fr', 21888242871839275222246405745257275088548364400416034343698204186575808495617),
            ('bls12-381.fr', 52435875175126190479447740508185965837690552500527637822603658699938581184513),
            ('ristretto255.scalar', 7237005577332262213973186563042994240857116359379907606001950938285454250989)]:
        add(['zkc.ring/0', [], [['constant', prime, str(modulus-1)]], [0]])
        add(['zkc.ring/0', [], [['constant', prime, str(modulus)]], [0]], False)
    # A scalar-field association must not admit a group, commitment or service
    # as a field in an expression arena.
    for nonfield in ['bls12-381.g1', 'bn254.gt', 'ristretto255.group',
                     'rows.merkle-keccak256.koala-bear/0',
                     'merlin3.koala-bear.ext8-binomial3.rejection31le/0']:
        add(['zkc.ring/0', [nonfield], [], []], False)
    for changed in [
            ['zkc.ring/1', [], [], []], ['zkc.ring/0', [], [], [], []],
            ['zkc.ring/0', [ext], [['input', 0], ['embed', field, 0]], [1]],
            ['zkc.ring/0', [field, ext], [['input', 0], ['input', 1], ['add', 0, 1]], [2]],
            ['zkc.ring/0', [], [['constant', field, '01']], [0]],
            ['zkc.ring/0', [], [['constant', ext, ['1'] * 8]], [0]],
            ['zkc.ring/0', ['unknown'], [], []]]:
        add(changed, False)
    changed = deepcopy(arena); changed[2][0] = ['input', 2]; add(changed, False)
    changed = deepcopy(arena); changed[2][2] = ['mul', 0, 3]; add(changed, False)
    changed = deepcopy(arena); changed[3] = [0]; add(changed, False)  # Dead nodes refuse.
    changed = deepcopy(arena); changed[3] = [3]; add(changed, False)
    for token in ['0.0', '-0', '00', '1e0', 'true', '18446744073709551616']:
        cases.append((f'["zkc.ring/0",["{field}"],[["input",{token}]],[0]]', False))
    rng = random.Random(20261009)
    for _ in range(80):
        nodes = [['input', 0], ['input', 1]]
        # Every root is retained, making shared and repeated edges intentional.
        for i in range(2, rng.randrange(3, 35)):
            if rng.randrange(3) == 0:
                nodes.append(['neg', rng.randrange(i)])
            else:
                nodes.append([rng.choice(['add', 'mul']), rng.randrange(i), rng.randrange(i)])
        add(['zkc.ring/0', [field, field], nodes, list(range(len(nodes)))])
    for count in [20, 21, 80]:
        nodes = [['input', 0]] + [['mul', i-1, i-1] for i in range(1, count+1)]
        add(['zkc.ring/0', [field], nodes, [count]])
    for count in [1023, 1024]:
        nodes = [['input', 0]] + [['neg', i-1] for i in range(1, count+1)]
        add(['zkc.ring/0', [field], nodes, [count]], count == 1023)
    wire = '\n'.join(row for row, _ in cases) + '\n'
    replies = []
    for executable in [toolchain.tool('compiler', 'test/zkc-ring_conformance-test'),
                       toolchain.driver('ring_conformance')]:
        replies.append([json.loads(line) for line in journal.run([executable], stdin=wire).splitlines()])
    assert replies[0] == replies[1]
    assert len(replies[0]) == len(cases)
    for (raw, admitted), answer in zip(cases, replies[0]):
        assert answer['accepted'] == admitted, (raw, answer)
        if admitted:
            assert answer['arena'] == json.loads(raw)
            assert answer['identity'] == sha256(raw.encode()).hexdigest()
