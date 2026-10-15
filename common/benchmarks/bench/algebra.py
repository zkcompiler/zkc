"""Untimed mathematical oracles, independent of the native backend libraries."""
import random

P = 2130706433
FR = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def dense(count, degree=1, seed=0, modulus=P):
    rng = random.Random(seed)
    return [tuple(rng.randrange(modulus) for _ in range(degree)) for _ in range(count)]


def add(a, b):
    return tuple((x + y) % P for x, y in zip(a, b, strict=True))


def mul(a, b):
    degree = len(a)
    assert degree == len(b) and degree in (1, 8)
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
