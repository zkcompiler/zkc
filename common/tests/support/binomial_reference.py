"""Integer arithmetic in KoalaBear[X]/(X^d - 3), independent of native code.

Elements are coordinate lists in the ascending basis (1, X, ..., X^(d-1)).
Multiplication is convolution followed by X^d = 3; nothing here calls the
native field implementation.
"""

P = 2130706433
NONRESIDUE = 3


class Binomial:
    def __init__(self, degree, nonresidue=NONRESIDUE):
        self.degree, self.nonresidue = degree, nonresidue
        self.ZERO = [0] * degree
        self.ONE = [1] + [0] * (degree - 1)

    def add(self, a, b):
        return [(x + y) % P for x, y in zip(a, b, strict=True)]

    def mul(self, a, b):
        d = self.degree
        result = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                result[i + j] += x * y
        for i in range(d, 2 * d - 1):
            result[i - d] += self.nonresidue * result[i]
        return [x % P for x in result[:d]]

    def power(self, a, exponent):
        result = self.ONE
        while exponent:
            if exponent % 2:
                result = self.mul(result, a)
            a, exponent = self.mul(a, a), exponent // 2
        return result

    def coordinates(self, value):
        return b''.join(x.to_bytes(4, 'little') for x in value)

    def embed(self, n):
        return [n % P] + [0] * (self.degree - 1)


OCTIC = Binomial(8)
QUARTIC = Binomial(4)
# Installed KoalaBear fields by extension degree; the base field is degree one.
FIELDS = {'koala-bear': Binomial(1), 'koala-bear.ext8-binomial3': OCTIC,
          'koala-bear.ext4-binomial3': QUARTIC}
