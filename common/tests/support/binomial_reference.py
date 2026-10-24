"""Integer arithmetic in F_p[X]/(X^d - nonresidue), independent of native code.

Elements are coordinate lists in the ascending basis (1, X, ..., X^(d-1)).
Multiplication is convolution followed by X^d = nonresidue; nothing here calls the
native field implementation.
"""

P = 2130706433
NONRESIDUE = 3


class Binomial:
    def __init__(self, degree, nonresidue=NONRESIDUE, *, modulus=P, coordinate_bytes=4):
        if degree < 1 or modulus < 2 or coordinate_bytes < 1:
            raise ValueError('invalid binomial presentation')
        if modulus > 1 << (8 * coordinate_bytes):
            raise ValueError('coordinate width cannot hold the modulus')
        self.degree, self.nonresidue = degree, nonresidue
        self.modulus, self.coordinate_bytes = modulus, coordinate_bytes
        self.ZERO = [0] * degree
        self.ONE = [1] + [0] * (degree - 1)

    def add(self, a, b):
        return [(x + y) % self.modulus for x, y in zip(a, b, strict=True)]

    def mul(self, a, b):
        d = self.degree
        result = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                result[i + j] += x * y
        for i in range(d, 2 * d - 1):
            result[i - d] += self.nonresidue * result[i]
        return [x % self.modulus for x in result[:d]]

    def power(self, a, exponent):
        if exponent < 0:
            raise ValueError('negative exponent')
        result = self.ONE
        while exponent:
            if exponent % 2:
                result = self.mul(result, a)
            a, exponent = self.mul(a, a), exponent // 2
        return result

    def coordinates(self, value):
        if len(value) != self.degree or any(not 0 <= x < self.modulus for x in value):
            raise ValueError('noncanonical coordinates')
        return b''.join(x.to_bytes(self.coordinate_bytes, 'little') for x in value)

    def embed(self, n):
        return [n % self.modulus] + [0] * (self.degree - 1)


OCTIC = Binomial(8)
QUARTIC = Binomial(4)
# Installed KoalaBear fields by extension degree; the base field is degree one.
FIELDS = {'koala-bear': Binomial(1), 'koala-bear.ext8-binomial3': OCTIC,
          'koala-bear.ext4-binomial3': QUARTIC}

# Keep FIELDS and the KoalaBear defaults stable: existing callers use P and
# four-byte coordinates alongside that inventory. New callers opt in explicitly.
PLONKY3_FIELDS = FIELDS | {
    'baby-bear': Binomial(1, modulus=2013265921),
    'baby-bear.ext4-binomial11': Binomial(4, 11, modulus=2013265921),
    'goldilocks': Binomial(1, modulus=18446744069414584321, coordinate_bytes=8),
    'goldilocks.ext2-binomial7': Binomial(2, 7, modulus=18446744069414584321,
                                      coordinate_bytes=8),
}
