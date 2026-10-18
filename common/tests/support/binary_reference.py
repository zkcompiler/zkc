"""Arithmetic in the installed binary fields, independent of native code.

The base field is GF(2)[x]/(x^64 + x^4 + x^3 + x + 1); an element is an
integer whose bit i is the coefficient of x^i. The cubic extension is
base[y]/(y^3 + y + 1); an element is three base elements in the basis
(1, y, y^2). Multiplication is shift-and-add with one reduction step per
shift; nothing here calls the native field implementation.
"""

BASE = 'gf2-64.pentanomial-4-3-1'
CUBIC = 'gf2-64.pentanomial-4-3-1.ext3-trinomial1'
MASK = (1 << 64) - 1
# x^64 = x^4 + x^3 + x + 1
TAIL = 0b11011


def times_x(a):
    return ((a << 1) & MASK) ^ (TAIL if a >> 63 else 0)


def mul(a, b):
    product = 0
    for i in range(64):
        if b >> i & 1:
            product ^= a
        a = times_x(a)
    return product


def power(a, exponent):
    result = 1
    while exponent:
        if exponent & 1:
            result = mul(result, a)
        a, exponent = mul(a, a), exponent >> 1
    return result


def inverse(a):
    return power(a, (1 << 64) - 2)


def cubic_add(a, b):
    return [x ^ y for x, y in zip(a, b, strict=True)]


def cubic_mul(a, b):
    c = [0] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] ^= mul(a[i], b[j])
    # y^3 = y + 1 and y^4 = y^2 + y.
    return [c[0] ^ c[3], c[1] ^ c[3] ^ c[4], c[2] ^ c[4]]


def cubic_power(a, exponent):
    result = [1, 0, 0]
    while exponent:
        if exponent & 1:
            result = cubic_mul(result, a)
        a, exponent = cubic_mul(a, a), exponent >> 1
    return result


def cubic_inverse(a):
    return cubic_power(a, (1 << 192) - 2)


def readable(value):
    """The readable Entry form: hexadecimal bit patterns, never decimals."""
    if isinstance(value, list):
        return [readable(x) for x in value]
    return hex(value)


def literal(value):
    """The canonical constant attribute: 0, 1 or a bit-pattern literal."""
    if isinstance(value, list):
        value = value[0] | value[1] << 64 | value[2] << 128
    return str(value) if value < 2 else hex(value)
