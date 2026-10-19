"""Independent affine BLS12-381 G1 arithmetic for Sigma regression controls.

Uses Python integers alone; neither the compiler nor its group provider supplies
the expected equation results. Points use the canonical compressed G1 encoding.
"""

P = int('1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab', 16)
ORDER = int('73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001', 16)


def point(value):
    wire = bytes.fromhex(value['bytes'])
    assert len(wire) == 48 and wire[0] & 0x80
    x = int.from_bytes(wire, 'big') & ((1 << 381) - 1)
    if wire[0] & 0x40:
        assert x == 0 and not wire[0] & 0x20
        return None
    assert x < P
    square = (x**3 + 4) % P
    y = pow(square, (P + 1) // 4, P)
    assert y * y % P == square
    if (y > P // 2) != bool(wire[0] & 0x20):
        y = P - y
    return x, y


def add(left, right):
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    u, v = right
    if x == u and (y + v) % P == 0:
        return None
    slope = ((3 * x * x) * pow(2 * y, -1, P) if left == right
             else (v - y) * pow(u - x, -1, P)) % P
    result = (slope * slope - x - u) % P
    return result, (slope * (x - result) - y) % P


def multiply(base, scalar):
    result = None
    scalar %= ORDER
    while scalar:
        if scalar & 1:
            result = add(result, base)
        base = add(base, base)
        scalar >>= 1
    return result


def accepts(public, scalars, nonces, challenge=17, delivered=17, response_delta=0):
    for i, prefix in enumerate(('first', 'second')):
        base, statement = (point(public[f'{prefix}_{name}']) for name in ('base', 'point'))
        response = (nonces[i] + delivered * scalars[i] + (response_delta if i == 0 else 0)) % ORDER
        if multiply(base, response) != add(multiply(base, nonces[i]),
                                           multiply(statement, challenge)):
            return False
    return True
