"""BabyBear Poseidon2-16 and the pinned duplex discipline.

The reference twin's independent implementation of the real execution
profile's primitive: nothing here reads the C++ implementation.  The round
constants and the known-answer test are transcribed mechanically from the
pinned upstream source (Plonky3 revision 3da346791c813433b201299afc3d10bf42f8a078,
`baby-bear/src/poseidon2.rs`: `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`,
`..._EXTERNAL_FINAL`, `..._INTERNAL`,
`test_default_babybear_poseidon2_width_16`), and the arithmetic follows the
upstream semantics (`poseidon2/src/external.rs` `mds_light_permutation` /
`MDSMat4`; `baby-bear/src/poseidon2.rs` `internal_layer_mat_mul`, the
diagonal `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27,
-1/2^8, -1/16, -1/2^27]`).  The module refuses to import if it cannot
reproduce the pinned known-answer test.

The duplex discipline mirrors the pinned DuplexChallenger (width 16, rate
8): buffered absorbs invalidate outputs; duplexing overwrites the first
`len` state slots, zeroes the rest of the rate, binds `len` into the first
capacity element, permutes, and refills the output buffer from the rate;
samples pop LIFO.  The declared squeeze domain is schedule metadata — the
pinned construction hashes no domain strings.
"""

from __future__ import annotations

P = 2013265921  # BabyBear: 2^31 - 2^27 + 1

RC_EXTERNAL_INITIAL = [
    [
        1774958255, 1185780729, 1621102414, 1796380621, 588815102, 1932426223,
        1925334750, 747903232, 89648862, 360728943, 977184635, 1425273457,
        256487465, 1200041953, 572403254, 448208942,
    ],
    [
        1215789478, 944884184, 953948096, 547326025, 646827752, 889997530,
        1536873262, 86189867, 1065944411, 32019634, 333311454, 456061748,
        1963448500, 1827584334, 1391160226, 1348741381,
    ],
    [
        88424255, 104111868, 1763866748, 79691676, 1988915530, 1050669594,
        359890076, 573163527, 222820492, 159256268, 669703072, 763177444,
        889367200, 256335831, 704371273, 25886717,
    ],
    [
        51754520, 1833211857, 454499742, 1384520381, 777848065, 1053320300,
        1851729162, 344647910, 401996362, 1046925956, 5351995, 1212119315,
        754867989, 36972490, 751272725, 506915399,
    ],
]

RC_EXTERNAL_FINAL = [
    [
        1922082829, 1870549801, 1502529704, 1990744480, 1700391016,
        1702593455, 321330495, 528965731, 183414327, 1886297254, 1178602734,
        1923111974, 744004766, 549271463, 1781349648, 542259047,
    ],
    [
        1536158148, 715456982, 503426110, 340311124, 1558555932, 1226350925,
        742828095, 1338992758, 1641600456, 1843351545, 301835475, 43203215,
        386838401, 1520185679, 1235297680, 904680097,
    ],
    [
        1491801617, 1581784677, 913384905, 247083962, 532844013, 107190701,
        213827818, 1979521776, 1358282574, 1681743681, 1867507480, 1530706910,
        507181886, 695185447, 1172395131, 1250800299,
    ],
    [
        1503161625, 817684387, 498481458, 494676004, 1404253825, 108246855,
        59414691, 744214112, 890862029, 1342765939, 1417398904, 1897591937,
        1066647396, 1682806907, 1015795079, 1619482808,
    ],
]

RC_INTERNAL = [
    1518359488, 1765533241, 945325693, 422793067, 311365592, 1311448267,
    1629555936, 1009879353, 190525218, 786108885, 557776863, 212616710,
    605745517,
]

_INV2 = (P + 1) // 2


def _sbox(x: int) -> int:
    x2 = x * x % P
    x3 = x2 * x % P
    return x3 * x3 % P * x % P


def _mat4(state: list[int], base: int) -> None:
    x0, x1, x2, x3 = state[base : base + 4]
    t01 = (x0 + x1) % P
    t23 = (x2 + x3) % P
    t0123 = (t01 + t23) % P
    t01123 = (t0123 + x1) % P
    t01233 = (t0123 + x3) % P
    state[base + 3] = (t01233 + 2 * x0) % P
    state[base + 1] = (t01123 + 2 * x2) % P
    state[base + 0] = (t01123 + t01) % P
    state[base + 2] = (t01233 + t23) % P


def _mds_light(state: list[int]) -> None:
    for chunk in range(0, 16, 4):
        _mat4(state, chunk)
    sums = [sum(state[j + k] for j in range(0, 16, 4)) % P for k in range(4)]
    for i in range(16):
        state[i] = (state[i] + sums[i % 4]) % P


_INTERNAL_DIAG = [
    P - 2, 1, 2, _INV2, 3, 4, P - _INV2, P - 3, P - 4,
    pow(_INV2, 8, P), pow(_INV2, 2, P), pow(_INV2, 3, P), pow(_INV2, 27, P),
    P - pow(_INV2, 8, P), P - pow(_INV2, 4, P), P - pow(_INV2, 27, P),
]


def permute(state: list[int]) -> None:
    """The default width-16 BabyBear Poseidon2 permutation, in place."""
    _mds_light(state)
    for round_constants in RC_EXTERNAL_INITIAL:
        for i in range(16):
            state[i] = _sbox((state[i] + round_constants[i]) % P)
        _mds_light(state)
    for round_constant in RC_INTERNAL:
        s0 = _sbox((state[0] + round_constant) % P)
        full_sum = (sum(state[1:]) + s0) % P
        state[0] = s0
        for i in range(16):
            state[i] = (state[i] * _INTERNAL_DIAG[i] + full_sum) % P
    for round_constants in RC_EXTERNAL_FINAL:
        for i in range(16):
            state[i] = _sbox((state[i] + round_constants[i]) % P)
        _mds_light(state)


class Duplex:
    """The pinned duplex over the permutation, with zkc's artifact-id iv:
    the source identity string is chunked into big-endian 32-bit words
    (a short final chunk keeps only the bytes present) and absorbed before
    any protocol event."""

    def __init__(self, source_identity: str):
        self.state = [0] * 16
        self.inputs: list[int] = []
        self.outputs: list[int] = []
        raw = source_identity.encode("ascii")
        for i in range(0, len(raw), 4):
            word = 0
            for byte in raw[i : i + 4]:
                word = (word << 8) | byte
            self.absorb_word(word)

    def absorb_word(self, word: int) -> None:
        self.outputs.clear()
        self.inputs.append(word % P)
        if len(self.inputs) == 8:
            self._duplexing()

    def squeeze_word(self) -> int:
        if self.inputs or not self.outputs:
            self._duplexing()
        return self.outputs.pop()

    def _duplexing(self) -> None:
        length = len(self.inputs)
        for i, value in enumerate(self.inputs):
            self.state[i] = value
        self.inputs.clear()
        if length > 0:
            for i in range(length, 8):
                self.state[i] = 0
            self.state[8] = (self.state[8] + length) % P
        permute(self.state)
        self.outputs = self.state[:8].copy()


_KAT_INPUT = [
    894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695,
    1717947831, 120589055, 19776022, 42382981, 1831865506, 724844064,
    171220207, 1299207443, 227047920, 1783754913,
]
_KAT_EXPECTED = [
    516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026,
    1788910906, 563338433, 319524748, 1741414159, 1650859320, 894311162,
    1121347488, 1692793758, 1052633829, 1344246938,
]

_state = list(_KAT_INPUT)
permute(_state)
if _state != _KAT_EXPECTED:
    raise AssertionError(
        "the twin's Poseidon2-16 permutation does not reproduce the pinned "
        "known-answer test"
    )
del _state
