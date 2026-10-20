"""Small integer polynomial oracle with generic Lagrange basis products.

The Lagrange calculation accepts arbitrary words and does not use a transform,
coset-specific evaluation weights, or any native implementation.
"""

from binomial_reference import FIELDS, P


BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617


class CosetReference:
    def __init__(self, field):
        if field != 'bn254.fr' and field not in FIELDS:
            raise ValueError(f'unsupported coset reference field: {field}')
        self.modulus = BN254 if field == 'bn254.fr' else P
        self.arithmetic = FIELDS.get(field)
        self.degree = self.arithmetic.degree if self.arithmetic else 1
        self.zero = (0,) * self.degree
        self.one = self.embed(1)

    def embed(self, value):
        return (value % self.modulus,) + (0,) * (self.degree - 1)

    def add(self, left, right):
        return tuple((x + y) % self.modulus for x, y in zip(left, right, strict=True))

    def sub(self, left, right):
        return tuple((x - y) % self.modulus for x, y in zip(left, right, strict=True))

    def mul(self, left, right):
        if self.arithmetic:
            return tuple(self.arithmetic.mul(left, right))
        return (left[0] * right[0] % self.modulus,)

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
        root = (pow(5, (self.modulus - 1) // height, self.modulus)
                if self.modulus == BN254 else
                pow(1791270792, (1 << 24) // height, self.modulus))
        assert pow(root, height, self.modulus) == 1
        assert height == 1 or pow(root, height // 2, self.modulus) != 1
        return [self.mul(shift, self.embed(pow(root, row, self.modulus)))
                for row in range(height)]

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
            inverse = self.power(denominator, self.modulus ** self.degree - 2)
            result = self.add(result, self.mul(value, self.mul(numerator, inverse)))
        return result
