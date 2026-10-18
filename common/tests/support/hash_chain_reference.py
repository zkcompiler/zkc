"""Independent reference for the native hash-chain transcript suites.

Keccak-f[1600] is written here from the Keccak reference, so the Keccak-256
used by the chain does not depend on any native or third-party hash code. The
chain, its framing, request expansion and the challenge decoders follow
docs/spec/ir/construction.md#native-hash-chain-suites.
"""
import json

from logical_tree import encode_tree

ROUND_CONSTANTS = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
# Rotation offsets r[x][y] of the rho step.
ROTATIONS = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]
MASK = (1 << 64) - 1


def rotate(value, count):
    return ((value << count) | (value >> (64 - count))) & MASK if count else value


def keccak_f1600(lanes):
    """The permutation on 25 lanes indexed `lanes[x + 5 * y]`."""
    a = [[lanes[x + 5 * y] for y in range(5)] for x in range(5)]
    for constant in ROUND_CONSTANTS:
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ rotate(c[(x + 1) % 5], 1) for x in range(5)]
        a = [[a[x][y] ^ d[x] for y in range(5)] for x in range(5)]
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = rotate(a[x][y], ROTATIONS[x][y])
        a = [[b[x][y] ^ (~b[(x + 1) % 5][y] & b[(x + 2) % 5][y]) for y in range(5)]
             for x in range(5)]
        a[0][0] ^= constant
    return [a[x][y] for y in range(5) for x in range(5)]


def sponge(data, *, rate, suffix, length):
    """A Keccak sponge with multi-rate padding after the domain `suffix` bits."""
    padded = bytearray(data) + bytes([suffix])
    padded += bytes(-len(padded) % rate)
    padded[-1] |= 0x80
    lanes = [0] * 25
    for start in range(0, len(padded), rate):
        block = padded[start:start + rate]
        for i in range(rate // 8):
            lanes[i] ^= int.from_bytes(block[8 * i:8 * i + 8], 'little')
        lanes = keccak_f1600(lanes)
    output = b''
    while len(output) < length:
        output += b''.join(lane.to_bytes(8, 'little') for lane in lanes[:rate // 8])
        if len(output) < length:
            lanes = keccak_f1600(lanes)
    return output[:length]


def keccak256(data):
    """Keccak-256 as used by Ethereum: rate 136, original padding byte 0x01."""
    return sponge(data, rate=136, suffix=0x01, length=32)


def sha3_256(data):
    """FIPS 202 SHA3-256, the same permutation with suffix 0x06; checks the
    permutation against Python's hashlib."""
    return sponge(data, rate=136, suffix=0x06, length=32)


HASHES = {'keccak256': keccak256}
BIND_TAG = b'zkc.hash-chain.bind/0\0'
ABSORB_TAG = b'zkc.hash-chain.absorb/0\0'
REQUEST_TAG = b'zkc.hash-chain.request/0\0'
FIXED, MESSAGE, REQUEST = 0, 1, 2


def frame(kind, label, data):
    return (bytes([kind]) + len(label).to_bytes(8, 'big') + label
            + len(data).to_bytes(8, 'big') + data)


def suite_hash(suite):
    """`hash-chain.<hash>.<field>.<decoder>/0` names its byte hash second."""
    construction, hash_name = suite.split('.')[:2]
    assert construction == 'hash-chain'
    return HASHES[hash_name]


class Chain:
    """The chain state and its primitive inputs, recorded in call order."""

    def __init__(self, suite, root):
        self.hash = suite_hash(suite)
        self.calls = []
        self.state = self.call(BIND_TAG + frame(FIXED, b'domain', b'zkc.artifact/0')
                               + frame(FIXED, b'suite', suite.encode())
                               + frame(MESSAGE, b'binding', root))

    def call(self, data):
        digest = self.hash(data)
        self.calls.append((data, digest))
        return digest

    def absorb(self, label, data):
        self.state = self.call(ABSORB_TAG + self.state + frame(MESSAGE, label, data))

    def request(self, label, length):
        event = frame(REQUEST, label, length.to_bytes(8, 'big'))
        blocks = (length + 31) // 32
        output = b''.join(self.call(REQUEST_TAG + self.state + event + k.to_bytes(8, 'big'))
                          for k in range(blocks))[:length]
        self.state = self.call(ABSORB_TAG + self.state + event)
        return output


BLS12_381_R = 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001
KOALA_BEAR_P = 2130706433


def fr64be(chain):
    """The wide big-endian reduction of one 64-byte request."""
    return int.from_bytes(chain.request(b'challenge', 64), 'big') % BLS12_381_R


def rejection31le(chain, degree=8, limit=16):
    """Masked 31-bit little-endian words; words at or above p are rejected."""
    coordinates = []
    for _ in range(limit):
        raw = chain.request(b'challenge', 64)
        for at in range(0, 64, 4):
            word = int.from_bytes(raw[at:at + 4], 'little') & 0x7FFFFFFF
            if word < KOALA_BEAR_P:
                coordinates.append(word)
                if len(coordinates) == degree:
                    return coordinates
    raise ValueError('challenge-rejection-limit')


def uniform_index(chain, bound):
    """UniformIndex(bound) for a power-of-two bound."""
    assert bound > 0 and bound & (bound - 1) == 0
    return int.from_bytes(chain.request(b'index', 64)[:8], 'little') & (bound - 1)


def native_origin(event):
    """A flat occurrence: no applications, repeats or coordinates."""
    return encode_tree(['zkc.native-origin/0', 'main', [], [], event])


BLS_SUITE = 'hash-chain.keccak256.bls12-381.fr64be/0'
OCTIC_SUITE = 'hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0'
VECTOR_ROOT = ['hash-chain-vector', 'source', 'descriptor', 'context', 'public', 'configuration']
# The canonical BLS12-381 Fr frame of 7 and the octic frame of (7, 0, ..., 0).
BLS_SEVEN = b'ZKCV\x00\x01' + bytes([7]) + bytes(31)
OCTIC_SEVEN = b'ZKCV\x00\x1a' + (7).to_bytes(4, 'little') + bytes(28)


def vectors():
    """Known answers for the backend tests: kernel-level events in order."""
    root = encode_tree(VECTOR_ROOT)
    suites = []
    for suite, contract, wire in [(BLS_SUITE, 'random.bls12-381.fr/0', BLS_SEVEN),
                                  (OCTIC_SUITE, 'random.koala-bear.ext8-binomial3/0', OCTIC_SEVEN)]:
        message = native_origin(['message', 'Source', 'message', 'Schema', 'P', 'V'])
        query = native_origin(['query', 'Source', 'draw', 'input_0', contract, 'draw', 'V'])
        chain = Chain(suite, root)
        steps = [{'state': chain.state.hex()}]

        def absorb(label, data):
            chain.absorb(label, data)
            steps.append({'absorb': [label.decode(), data.hex()], 'state': chain.state.hex()})

        def request(label):
            output = chain.request(label, 64)
            steps.append({'request': [label.decode(), 64], 'output': output.hex(),
                          'state': chain.state.hex()})
            return output

        absorb(b'origin', message)
        absorb(b'value', wire)
        absorb(b'origin', query)
        entry = {'suite': suite, 'root': root.hex(), 'message': message.hex(),
                 'query': query.hex(), 'wire': wire.hex()}
        if suite == BLS_SUITE:
            first = request(b'challenge')
            # Two requests with no event between them still differ: each
            # request advances the state.
            second = request(b'challenge')
            entry['challenges'] = [str(int.from_bytes(raw, 'big') % BLS12_381_R)
                                   for raw in (first, second)]
        else:
            raw = request(b'challenge')
            words = [int.from_bytes(raw[at:at + 4], 'little') & 0x7FFFFFFF for at in range(0, 64, 4)]
            assert all(w < KOALA_BEAR_P for w in words[:8])
            entry['challenge'] = words[:8]
            index = native_origin(['query', 'Source', 'pick', 'input_0', contract, 'index', 'V'])
            entry['index_query'] = index.hex()
            absorb(b'origin', index)
            absorb(b'bound', (256).to_bytes(8, 'little'))
            output = request(b'index')
            entry['index'] = int.from_bytes(output[:8], 'little') & 255
            entry['bound'] = 256
        entry['steps'] = steps
        suites.append(entry)
    return {'format': 'zkc.hash-chain-vectors/0',
            'keccak256': {text: keccak256(text.encode()).hex() for text in ['', 'abc']},
            'suites': suites}


def render(value):
    return json.dumps(value, indent=1) + '\n'
