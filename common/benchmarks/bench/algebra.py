"""Untimed mathematical oracles, independent of the native backend libraries."""
import random
from functools import cache
import importlib.util
from pathlib import Path

P = 2130706433
FR = 52435875175126190479447740508185965837690552500527637822603658699938581184513
BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
DALEK_SCALAR = 2**252 + 27742317777372353535851937790883648493


def dense(count, degree=1, seed=0, modulus=P):
    rng = random.Random(seed)
    return [tuple(rng.randrange(modulus) for _ in range(degree)) for _ in range(count)]


def add(a, b):
    return tuple((x + y) % P for x, y in zip(a, b, strict=True))


def mul(a, b):
    degree = len(a)
    assert degree == len(b) and degree in (1, 4, 8)
    result = [0] * (2 * degree - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    for i in range(degree, len(result)):
        result[i - degree] += 3 * result[i]
    return tuple(x % P for x in result[:degree])


def horner(coefficients, at):
    value = (0,) * len(at)
    for coefficient in reversed(coefficients):
        value = add(mul(value, at), coefficient)
    return value


def coset(coefficients, shift, size):
    """Radix-two evaluation, natural order; all coordinates participate."""
    assert size > 0 and size & (size - 1) == 0 and size <= 1 << 24
    assert len(coefficients) <= size
    degree = len(shift)
    values = [(0,) * degree for _ in range(size)]
    power = (1,) + (0,) * (degree - 1)
    bits = size.bit_length() - 1
    for i, coefficient in enumerate(coefficients):
        index = int(f'{i:0{bits}b}'[::-1], 2) if bits else 0
        values[index] = mul(coefficient, power)
        power = mul(power, shift)
    width = 2
    while width <= size:
        root = pow(1791270792, (1 << 24) // width, P)
        for start in range(0, size, width):
            twiddle = 1
            for j in range(width // 2):
                a, b = values[start + j], values[start + j + width // 2]
                b = tuple(x * twiddle % P for x in b)
                values[start + j] = add(a, b)
                values[start + j + width // 2] = tuple((x - y) % P for x, y in zip(a, b, strict=True))
                twiddle = twiddle * root % P
        width *= 2
    return values


def encode(value):
    return str(value[0]) if len(value) == 1 else list(map(str, value))


BINARY = 'gf2-64.pentanomial-4-3-1'
BINARY_CUBIC = BINARY + '.ext3-trinomial1'
BINARY_REFERENCE = Path(__file__).resolve().parents[2]/'tests/support/binary_reference.py'


@cache
def binary_reference(path=BINARY_REFERENCE):
    """Reuse the maintained shift-and-add oracle, also captured as an input."""
    spec = importlib.util.spec_from_file_location('benchmark_binary_reference', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class FieldOracle:
    """Scalar arithmetic and readable codecs, never an expression evaluator."""

    def __init__(self, field, *, root=None):
        self.degree = {'koala-bear': 1, 'bls12-381.fr': 1, 'bn254.fr': 1, 'ristretto255.scalar': 1,
                       'koala-bear.ext4-binomial3': 4, 'koala-bear.ext8-binomial3': 8,
                       BINARY: 1, BINARY_CUBIC: 3}[field]
        self.binary = field in (BINARY, BINARY_CUBIC)
        self.modulus = ((1 << 64) if self.binary else
                        {'bls12-381.fr': FR, 'bn254.fr': BN254,
                         'ristretto255.scalar': DALEK_SCALAR}.get(field, P))
        self.zero = (0,) * self.degree
        self.one = (1,) + (0,) * (self.degree - 1)
        reference = BINARY_REFERENCE if root is None else root/'common/tests/support/binary_reference.py'
        self.support = (reference,) if self.binary else ()

    def add(self, x, y):
        return tuple(u ^ v if self.binary else (u + v) % self.modulus
                     for u, v in zip(x, y, strict=True))

    def sub(self, x, y):
        return self.add(x, y) if self.binary else tuple((u - v) % self.modulus
                                                       for u, v in zip(x, y, strict=True))

    def mul(self, x, y):
        if self.binary:
            ref = binary_reference(self.support[0])
            return (ref.mul(x[0], y[0]),) if self.degree == 1 else tuple(ref.cubic_mul(x, y))
        return (x[0] * y[0] % self.modulus,) if self.degree == 1 else mul(x, y)

    def power(self, x, exponent):
        result = self.one
        while exponent:
            if exponent & 1:
                result = self.mul(result, x)
            x, exponent = self.mul(x, x), exponent >> 1
        return result

    def dense(self, count, seed):
        return dense(count, self.degree, seed, self.modulus)

    def encode(self, value):
        if self.binary:
            return hex(value[0]) if self.degree == 1 else list(map(hex, value))
        return encode(value)
