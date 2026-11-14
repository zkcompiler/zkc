#!/usr/bin/env python3
"""An independent replay of the derived Schnorr proof.

The scheme is `scheme Proof = Schnorr<G1>: construction derived(Merlin3Bls12381)` of
`examples/schnorr_example.zkc`, with the layout `zkc::layout::canonical`. The script
computes the proof that the prover's program writes for a statement, a witness and a nonce from
published definitions and the schedule of the derived construction, written out below; it uses
nothing of zkc's code and only Python's standard library.

The definitions:

- Keccak-f[1600] as FIPS 202 states it (section 3.2): the rotation offsets of rho and the round
  constants of iota are computed by the standard's own procedures, not copied;
- STROBE-128, protocol version 1.0.2 (security 128, so the rate is 200 - 2*16 - 2 = 166 bytes);
- Merlin 1.0: STROBE-128 with the label "Merlin v1.0", then the transcript's label appended
  under "dom-sep"; `append_message(label, message)` is the label as metadata, the length of the
  message in four bytes, least significant first, as metadata continued, and the message as
  associated data; `challenge_bytes(label, n)` is the label and `n` likewise, then PRF of `n`;
- BLS12-381 G1 (draft-irtf-cfrg-pairing-friendly-curves-11, section 4.2.1) in affine
  coordinates, and the compressed form of its ZCash serialization format (appendix C): `x` in 48
  bytes, most significant first, the flags 0x80 (compressed), 0x40 (the point at infinity) and
  0x20 (`y` greater than (p - 1) / 2) in the first byte.

The schedule, for the suite `suite.merlin3.bls12-381.fr64be/0`:

1. `Transcript::new(b"suite.merlin3.bls12-381.fr64be/0")`;
2. `append_message(b"identity", identity)`, the 32 bytes of the proof identity;
3. the statement: `base`, then `point`, each under the label `[0, position]`;
4. the commitment `R = nonce * base` under the label of its site;
5. the challenge: `challenge_bytes(label of its site, 64)`, read most significant first,
   modulo the order `r` of G1;
6. the response `z = nonce + challenge * witness` modulo `r` under the label of its site.

A label is its numbers, each in eight bytes, least significant first; the label of a site is
`[1, definition, site, prover, verifier]`. A value is absorbed as the bytes that the layout
writes for it: a point compressed, a scalar in 32 bytes, least significant first. The proof is
the layout's bytes of the prover's messages, `R` then `z`.

The proof identity is an input: it is the SHA-256 of the package and the declaration, which
this script does not rebuild. The numbers of the definition, of the sites and of the roles
default to those of the program as the frontend emits it: definition 0, the sites 1
(commitment), 2 (challenge) and 3 (response), the prover 0 and the verifier 1.

usage: python3 -I replay_derived_schnorr.py --identity HEX --base K --point K --witness X
           --nonce N [--definition D] [--sites C,H,R] [--roles P,V] [--schedule]

`--base K` and `--point K` are multiples of the generator of G1. It prints the proof in
hexadecimal; with `--schedule`, every operation of the transcript with its bytes before it.
Before anything it checks its Keccak-f against SHA3-256 of the empty message, its Merlin against
Merlin's published conformance vector, and its compressed form against a published vector of
the ZCash format.
"""

import argparse
import hashlib
import sys

# ------------------------------------------------------------------ Keccak-f[1600], FIPS 202


def round_constant_bit(t):
    """rc(t) of FIPS 202, Algorithm 5: a linear feedback shift register."""
    if t % 255 == 0:
        return 1
    register = [1, 0, 0, 0, 0, 0, 0, 0]
    for _ in range(t % 255):
        register = [0] + register
        feedback = register[8]
        register[0] ^= feedback
        register[4] ^= feedback
        register[5] ^= feedback
        register[6] ^= feedback
        register = register[:8]
    return register[0]


def round_constant(index):
    """The constant of iota for a round: bit 2^j - 1 is rc(j + 7 * index)."""
    value = 0
    for j in range(7):
        if round_constant_bit(j + 7 * index):
            value |= 1 << ((1 << j) - 1)
    return value


def rotation_offsets():
    """The offsets of rho, FIPS 202 Algorithm 2: lane (x, y) at index x + 5 y."""
    offsets = [0] * 25
    x, y = 1, 0
    for t in range(24):
        offsets[x + 5 * y] = ((t + 1) * (t + 2) // 2) % 64
        x, y = y, (2 * x + 3 * y) % 5
    return offsets


ROUND_CONSTANTS = [round_constant(index) for index in range(24)]
OFFSETS = rotation_offsets()
LANE = (1 << 64) - 1


def rotl(lane, count):
    count %= 64
    return ((lane << count) | (lane >> (64 - count))) & LANE


def permutation(state):
    """Keccak-f[1600] on 200 bytes, a lane being eight bytes, least significant first."""
    lanes = [int.from_bytes(state[8 * i:8 * i + 8], "little") for i in range(25)]
    for constant in ROUND_CONSTANTS:
        # theta
        parity = [lanes[x] ^ lanes[x + 5] ^ lanes[x + 10] ^ lanes[x + 15] ^ lanes[x + 20]
                  for x in range(5)]
        lanes = [lanes[i] ^ parity[(i % 5 - 1) % 5] ^ rotl(parity[(i % 5 + 1) % 5], 1)
                 for i in range(25)]
        # rho and pi: A'[x, y] = A[(x + 3 y) mod 5, x], each lane rotated first
        rotated = [rotl(lanes[i], OFFSETS[i]) for i in range(25)]
        moved = [0] * 25
        for x in range(5):
            for y in range(5):
                moved[x + 5 * y] = rotated[(x + 3 * y) % 5 + 5 * x]
        # chi
        lanes = [moved[x + 5 * y] ^ ((~moved[(x + 1) % 5 + 5 * y] & LANE) & moved[(x + 2) % 5 + 5 * y])
                 for y in range(5) for x in range(5)]
        # iota
        lanes[0] ^= constant
    return bytearray(b"".join(lane.to_bytes(8, "little") for lane in lanes))


def sha3_256_of_empty():
    state = bytearray(200)
    state[0] ^= 0x06
    state[135] ^= 0x80
    return bytes(permutation(state)[:32])


# ------------------------------------------------------------------ STROBE-128 and Merlin 1.0

RATE = 166
I_FLAG, A_FLAG, C_FLAG, M_FLAG, K_FLAG = 0x01, 0x02, 0x04, 0x10, 0x20


class Strobe128:
    def __init__(self, protocol):
        state = bytearray(200)
        state[0:6] = bytes([1, RATE + 2, 1, 0, 1, 12 * 8])
        state[6:18] = b"STROBEv1.0.2"
        self.state = permutation(state)
        self.position = 0
        self.position_begin = 0
        self.flags = 0
        self.operate(M_FLAG | A_FLAG, protocol, False)

    def run_f(self):
        self.state[self.position] ^= self.position_begin
        self.state[self.position + 1] ^= 0x04
        self.state[RATE + 1] ^= 0x80
        self.state = permutation(self.state)
        self.position = 0
        self.position_begin = 0

    def duplex(self, data, squeeze):
        out = bytearray()
        for byte in data:
            if squeeze:
                out.append(self.state[self.position])
                self.state[self.position] = 0
            else:
                self.state[self.position] ^= byte
            self.position += 1
            if self.position == RATE:
                self.run_f()
        return bytes(out)

    def begin(self, flags):
        previous = self.position_begin
        self.position_begin = self.position + 1
        self.flags = flags
        self.duplex(bytes([previous, flags]), False)
        if flags & (C_FLAG | K_FLAG) and self.position != 0:
            self.run_f()

    def operate(self, flags, data, more):
        """An operation: absorb `data`, or squeeze `len(data)` bytes for PRF."""
        if not more:
            self.begin(flags)
        elif flags != self.flags:
            raise ValueError("a continued operation with other flags")
        return self.duplex(data, flags & C_FLAG and flags & I_FLAG)


class Transcript:
    def __init__(self, label, log):
        self.log = log
        self.strobe = Strobe128(b"Merlin v1.0")
        self.append_message(b"dom-sep", label)

    def append_message(self, label, message):
        self.log.append(("append", label, bytes(message)))
        self.strobe.operate(M_FLAG | A_FLAG, label, False)
        self.strobe.operate(M_FLAG | A_FLAG, len(message).to_bytes(4, "little"), True)
        self.strobe.operate(A_FLAG, message, False)

    def challenge_bytes(self, label, count):
        self.strobe.operate(M_FLAG | A_FLAG, label, False)
        self.strobe.operate(M_FLAG | A_FLAG, count.to_bytes(4, "little"), True)
        out = self.strobe.operate(I_FLAG | A_FLAG | C_FLAG, bytes(count), False)
        self.log.append(("challenge", label, out))
        return out


def merlin_conformance():
    """The conformance vector of Merlin 1.0."""
    transcript = Transcript(b"test protocol", [])
    transcript.append_message(b"some label", b"some data")
    return transcript.challenge_bytes(b"challenge", 32).hex() == (
        "d5a21972d0d5fe320c0d263fac7fffb8145aa640af6e9bca177c03c7efcf0615")


# ------------------------------------------------------------------ BLS12-381 G1

P = int("1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eab"
        "fffeb153ffffb9feffffffffaaab", 16)
R = int("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001", 16)
GENERATOR = (
    int("17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83f"
        "f97a1aeffb3af00adb22c6bb", 16),
    int("08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744"
        "a2888ae40caa232946c5e7e1", 16),
)


def point_sum(first, second):
    if first is None:
        return second
    if second is None:
        return first
    if first[0] == second[0]:
        if (first[1] + second[1]) % P == 0:
            return None
        slope = 3 * first[0] * first[0] * pow(2 * first[1], -1, P) % P
    else:
        slope = (second[1] - first[1]) * pow(second[0] - first[0], -1, P) % P
    x = (slope * slope - first[0] - second[0]) % P
    return (x, (slope * (first[0] - x) - first[1]) % P)


def times(point, scalar):
    total = None
    for bit in bin(scalar)[2:]:
        total = point_sum(total, total)
        if bit == "1":
            total = point_sum(total, point)
    return total


def compressed(point):
    if point is None:
        return bytes([0xC0]) + bytes(47)
    flags = 0x80 | (0x20 if point[1] > (P - 1) // 2 else 0)
    encoded = point[0].to_bytes(48, "big")
    return bytes([encoded[0] | flags]) + encoded[1:]


def decompressed(encoded):
    """The point of a compressed encoding with neither the infinity nor any other flag misused."""
    flags = encoded[0] & 0xE0
    x = int.from_bytes(bytes([encoded[0] & 0x1F]) + encoded[1:], "big")
    if flags not in (0x80, 0xA0) or x >= P:
        return None
    y = pow((x ** 3 + 4) % P, (P + 1) // 4, P)
    if y * y % P != (x ** 3 + 4) % P:
        return None
    if (y > (P - 1) // 2) != bool(flags & 0x20):
        y = P - y
    return (x, y)


def format_conformance():
    """A published vector of the ZCash format: `deserialization_succeeds_correct_point` of
    `case08_deserialization_G1` in github.com/ethereum/bls12-381-tests, read and written back."""
    published = bytes.fromhex(
        "a491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a")
    point = decompressed(published)
    return point is not None and times(point, R) is None and compressed(point) == published


# ------------------------------------------------------------------ the schedule


def label(numbers):
    return b"".join(number.to_bytes(8, "little") for number in numbers)


def scalar_bytes(value):
    return (value % R).to_bytes(32, "little")


def prove(identity, base, point, witness, nonce, definition, sites, roles, log):
    commitment_site, challenge_site, response_site = sites
    prover, verifier = roles
    transcript = Transcript(b"suite.merlin3.bls12-381.fr64be/0", log)
    transcript.append_message(b"identity", identity)
    transcript.append_message(label([0, 0]), compressed(base))
    transcript.append_message(label([0, 1]), compressed(point))
    commitment = times(base, nonce % R)
    transcript.append_message(label([1, definition, commitment_site, prover, verifier]),
                              compressed(commitment))
    squeezed = transcript.challenge_bytes(
        label([1, definition, challenge_site, prover, verifier]), 64)
    challenge = int.from_bytes(squeezed, "big") % R
    response = (nonce + challenge * witness) % R
    transcript.append_message(label([1, definition, response_site, prover, verifier]),
                              scalar_bytes(response))
    return compressed(commitment) + scalar_bytes(response)


def main():
    parser = argparse.ArgumentParser(description="an independent replay of the derived Schnorr proof")
    parser.add_argument("--identity", required=True)
    parser.add_argument("--base", type=int, required=True)
    parser.add_argument("--point", type=int, required=True)
    parser.add_argument("--witness", type=lambda text: int(text, 0), required=True)
    parser.add_argument("--nonce", type=lambda text: int(text, 0), required=True)
    parser.add_argument("--definition", type=int, default=0)
    parser.add_argument("--sites", default="1,2,3")
    parser.add_argument("--roles", default="0,1")
    parser.add_argument("--schedule", action="store_true")
    arguments = parser.parse_args()
    if sha3_256_of_empty() != hashlib.sha3_256(b"").digest():
        print("Keccak-f does not give SHA3-256 of the empty message", file=sys.stderr)
        return 1
    if not merlin_conformance():
        print("Merlin does not give its conformance vector", file=sys.stderr)
        return 1
    if not format_conformance():
        print("the compressed form does not read and write the published vector", file=sys.stderr)
        return 1
    log = []
    proof = prove(bytes.fromhex(arguments.identity), times(GENERATOR, arguments.base),
                  times(GENERATOR, arguments.point), arguments.witness, arguments.nonce,
                  arguments.definition, [int(site) for site in arguments.sites.split(",")],
                  [int(role) for role in arguments.roles.split(",")], log)
    if arguments.schedule:
        for kind, name, data in log:
            shown = name.decode() if all(32 <= byte < 127 for byte in name) else name.hex()
            print(f"{kind} under {shown} ({len(name)} bytes): {data.hex()} ({len(data)} bytes)")
    print(proof.hex())
    return 0


if __name__ == "__main__":
    sys.exit(main())
