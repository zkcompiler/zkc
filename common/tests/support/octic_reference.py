"""Integer arithmetic in KoalaBear[X]/(X^8 - 3), independent of native code."""

P = 2130706433
ZERO = [0] * 8
ONE = [1] + [0] * 7


def add(a, b):
    return [(x + y) % P for x, y in zip(a, b, strict=True)]


def mul(a, b):
    result = [0] * 15
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    for i in range(8, 15):
        result[i - 8] += 3 * result[i]
    return [x % P for x in result[:8]]


def power(a, exponent):
    result = ONE
    while exponent:
        if exponent % 2:
            result = mul(result, a)
        a, exponent = mul(a, a), exponent // 2
    return result


def coordinates(value):
    return b''.join(x.to_bytes(4, 'little') for x in value)
