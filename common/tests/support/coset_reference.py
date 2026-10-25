"""Small integer polynomial oracle with generic Lagrange basis products.

The Lagrange calculation accepts arbitrary words and does not use a transform,
coset-specific evaluation weights, or any native implementation.
"""

from binomial_reference import Binomial


BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617

# Independently specified (modulus, degree, binomial constant, base root, base log).
# Extension subgroup maxima are deliberately not used for these cosets.
FIELDS = {
    "bn254.fr": (BN254, 1, 0, pow(5, (BN254 - 1) // (1 << 28), BN254), 28),
    "koala-bear": (2130706433, 1, 0, 1791270792, 24),
    "koala-bear.ext4-binomial3": (2130706433, 4, 3, 1791270792, 24),
    "koala-bear.ext8-binomial3": (2130706433, 8, 3, 1791270792, 24),
    "baby-bear": (2013265921, 1, 0, 440564289, 27),
    "baby-bear.ext4-binomial11": (2013265921, 4, 11, 440564289, 27),
    "goldilocks": (18446744069414584321, 1, 0, 1753635133440165772, 32),
    "goldilocks.ext2-binomial7": (18446744069414584321, 2, 7, 1753635133440165772, 32),
}


class CosetReference:
    def __init__(self, field):
        if field not in FIELDS:
            raise ValueError(f"unsupported coset reference field: {field}")
        self.modulus, self.degree, nonresidue, self.base_root, self.base_log = FIELDS[
            field
        ]
        self.arithmetic = Binomial(
            self.degree,
            nonresidue,
            modulus=self.modulus,
            coordinate_bytes=(self.modulus.bit_length() + 7) // 8,
        )
        self.zero = (0,) * self.degree
        self.one = self.embed(1)

    def embed(self, value):
        return (value % self.modulus,) + (0,) * (self.degree - 1)

    def add(self, left, right):
        return tuple((x + y) % self.modulus for x, y in zip(left, right, strict=True))

    def sub(self, left, right):
        return tuple((x - y) % self.modulus for x, y in zip(left, right, strict=True))

    def mul(self, left, right):
        return tuple(self.arithmetic.mul(left, right))

    def power(self, value, exponent):
        result = self.one
        while exponent:
            if exponent & 1:
                result = self.mul(result, value)
            value, exponent = self.mul(value, value), exponent >> 1
        return result

    def encode(self, value):
        return str(value[0]) if self.degree == 1 else list(map(str, value))

    def domain(self, shift, height):
        if height < 1 or height & (height - 1) or height > 1 << self.base_log:
            raise ValueError("invalid base subgroup size")
        root = pow(self.base_root, (1 << self.base_log) // height, self.modulus)
        assert pow(root, height, self.modulus) == 1
        assert height == 1 or pow(root, height // 2, self.modulus) != 1
        return [
            self.mul(shift, self.embed(pow(root, row, self.modulus)))
            for row in range(height)
        ]

    def horner(self, coefficients, point):
        result = self.zero
        for coefficient in reversed(coefficients):
            result = self.add(self.mul(result, point), coefficient)
        return result

    def lagrange(self, values, domain, point):
        result = self.zero
        for row, (value, x) in enumerate(zip(values, domain, strict=True)):
            numerator, denominator = self.one, self.one
            for other, y in enumerate(domain):
                if row != other:
                    numerator = self.mul(numerator, self.sub(point, y))
                    denominator = self.mul(denominator, self.sub(x, y))
            assert denominator != self.zero
            inverse = self.power(denominator, self.modulus**self.degree - 2)
            result = self.add(result, self.mul(value, self.mul(numerator, inverse)))
        return result
