"""The exact finite field and binary-fold arithmetic used by the witness.

The base field is ``F_97``.  The extension is ``F_97[u] / (u^2 - 5)``;
``5`` is a quadratic non-residue modulo ``97``.  Constructors accept only
canonical representatives.  Call :meth:`Fp.reduce` when modular reduction is
intended explicitly.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .terms import ModelFailure, ResourceCounter, malformed, refusal


MODULUS = 97
PRIMITIVE_GENERATOR = 5
EXTENSION_NONRESIDUE = 5
BINARY_FOLD_FIELD_OPERATIONS = 8
POLYNOMIAL_COEFFICIENT_FIELD_OPERATIONS = 2
MAX_POLYNOMIAL_COEFFICIENTS = 8


def _require_fp_operand(value: Any) -> "Fp":
    if not isinstance(value, Fp):
        raise malformed(
            "field:operand",
            "FRI-IOR-FIELD-002",
            "a base-field operation requires an Fp operand",
        )
    return value


@dataclass(frozen=True, slots=True)
class Fp:
    """A canonical element of ``F_97``."""

    value: int

    def __post_init__(self) -> None:
        if type(self.value) is not int or not 0 <= self.value < MODULUS:
            raise malformed(
                "field:formation",
                "FRI-IOR-FIELD-001",
                "an Fp representative must be an integer in [0, 97)",
            )

    @classmethod
    def reduce(cls, value: int) -> "Fp":
        if type(value) is not int:
            raise malformed(
                "field:formation",
                "FRI-IOR-FIELD-001",
                "only an integer can be reduced into Fp",
            )
        return cls(value % MODULUS)

    @classmethod
    def from_bytes(cls, encoded: bytes) -> "Fp":
        if not isinstance(encoded, bytes) or len(encoded) != 1:
            raise malformed(
                "field:codec",
                "FRI-IOR-FIELD-003",
                "the finite profile encodes an Fp element as exactly one byte",
            )
        if encoded[0] >= MODULUS:
            raise malformed(
                "field:codec",
                "FRI-IOR-FIELD-003",
                "an encoded Fp byte must be the canonical representative below 97",
            )
        return cls(encoded[0])

    def to_bytes(self) -> bytes:
        return bytes((self.value,))

    def __int__(self) -> int:
        return self.value

    def __add__(self, other: Any) -> "Fp":
        operand = _require_fp_operand(other)
        return Fp.reduce(self.value + operand.value)

    def __sub__(self, other: Any) -> "Fp":
        operand = _require_fp_operand(other)
        return Fp.reduce(self.value - operand.value)

    def __mul__(self, other: Any) -> "Fp":
        operand = _require_fp_operand(other)
        return Fp.reduce(self.value * operand.value)

    def __neg__(self) -> "Fp":
        return Fp.reduce(-self.value)

    def __pow__(self, exponent: int) -> "Fp":
        if type(exponent) is not int or exponent < 0:
            raise malformed(
                "field:exponentiation",
                "FRI-IOR-FIELD-004",
                "an Fp exponent must be a non-negative integer",
            )
        return Fp(pow(self.value, exponent, MODULUS))

    def inverse(self) -> "Fp":
        if self.value == 0:
            raise refusal(
                "field:inverse",
                "FRI-IOR-FIELD-005",
                "zero has no multiplicative inverse",
            )
        return Fp(pow(self.value, MODULUS - 2, MODULUS))

    def __truediv__(self, other: Any) -> "Fp":
        return self * _require_fp_operand(other).inverse()


def _require_fp2_operand(value: Any) -> "Fp2":
    if not isinstance(value, Fp2):
        raise malformed(
            "field:operand",
            "FRI-IOR-FIELD-006",
            "an extension-field operation requires an Fp2 operand",
        )
    return value


@dataclass(frozen=True, slots=True)
class Fp2:
    """An element ``real + imag*u`` with ``u^2 = 5``."""

    real: Fp
    imag: Fp

    def __post_init__(self) -> None:
        if not isinstance(self.real, Fp) or not isinstance(self.imag, Fp):
            raise malformed(
                "field:formation",
                "FRI-IOR-FIELD-007",
                "Fp2 coefficients must both be canonical Fp elements",
            )

    @classmethod
    def from_base(cls, value: Fp) -> "Fp2":
        return cls(_require_fp_operand(value), Fp(0))

    @classmethod
    def zero(cls) -> "Fp2":
        return cls(Fp(0), Fp(0))

    @classmethod
    def one(cls) -> "Fp2":
        return cls(Fp(1), Fp(0))

    @classmethod
    def from_bytes(cls, encoded: bytes) -> "Fp2":
        if not isinstance(encoded, bytes) or len(encoded) != 2:
            raise malformed(
                "field:codec",
                "FRI-IOR-FIELD-008",
                "the finite profile encodes an Fp2 element as exactly two bytes",
            )
        return cls(Fp.from_bytes(encoded[:1]), Fp.from_bytes(encoded[1:]))

    def to_bytes(self) -> bytes:
        return self.real.to_bytes() + self.imag.to_bytes()

    def to_term(self) -> list[int]:
        return [self.real.value, self.imag.value]

    def __add__(self, other: Any) -> "Fp2":
        operand = _require_fp2_operand(other)
        return Fp2(self.real + operand.real, self.imag + operand.imag)

    def __sub__(self, other: Any) -> "Fp2":
        operand = _require_fp2_operand(other)
        return Fp2(self.real - operand.real, self.imag - operand.imag)

    def __neg__(self) -> "Fp2":
        return Fp2(-self.real, -self.imag)

    def __mul__(self, other: Any) -> "Fp2":
        operand = _require_fp2_operand(other)
        nonresidue = Fp(EXTENSION_NONRESIDUE)
        return Fp2(
            self.real * operand.real + nonresidue * self.imag * operand.imag,
            self.real * operand.imag + self.imag * operand.real,
        )

    def scale(self, scalar: Fp) -> "Fp2":
        base = _require_fp_operand(scalar)
        return Fp2(self.real * base, self.imag * base)

    def __pow__(self, exponent: int) -> "Fp2":
        if type(exponent) is not int or exponent < 0:
            raise malformed(
                "field:exponentiation",
                "FRI-IOR-FIELD-009",
                "an Fp2 exponent must be a non-negative integer",
            )
        result = Fp2.one()
        base = self
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = result * base
            base = base * base
            remaining >>= 1
        return result

    def inverse(self) -> "Fp2":
        nonresidue = Fp(EXTENSION_NONRESIDUE)
        norm = self.real * self.real - nonresidue * self.imag * self.imag
        if norm == Fp(0):
            raise refusal(
                "field:inverse",
                "FRI-IOR-FIELD-010",
                "zero has no extension-field inverse",
            )
        inverse_norm = norm.inverse()
        return Fp2(self.real * inverse_norm, -self.imag * inverse_norm)

    def __truediv__(self, other: Any) -> "Fp2":
        return self * _require_fp2_operand(other).inverse()


def binary_fold(
    point: Fp,
    positive: Fp2,
    negative: Fp2,
    challenge: Fp2,
    resources: ResourceCounter | None = None,
) -> Fp2:
    """Fold evaluations at ``x`` and ``-x`` onto the point ``x^2``.

    For ``f(X) = f_even(X^2) + X*f_odd(X^2)``, this returns
    ``f_even(x^2) + challenge*f_odd(x^2)``.  The occurrence order is part of
    the API: ``positive`` is the value at ``x`` and ``negative`` the value at
    ``-x``.
    """

    base_point = _require_fp_operand(point)
    positive_value = _require_fp2_operand(positive)
    negative_value = _require_fp2_operand(negative)
    beta = _require_fp2_operand(challenge)
    if base_point == Fp(0):
        raise refusal(
            "field:binary-fold",
            "FRI-IOR-FIELD-011",
            "binary folding is undefined at the zero evaluation point",
        )
    if resources is not None:
        if not isinstance(resources, ResourceCounter):
            raise malformed(
                "field:binary-fold",
                "FRI-IOR-FIELD-012",
                "binary folding requires a ResourceCounter when metered",
            )
        resources.consume_field_operations(BINARY_FOLD_FIELD_OPERATIONS)

    inverse_two = Fp(2).inverse()
    even = (positive_value + negative_value).scale(inverse_two)
    inverse_two_x = (Fp(2) * base_point).inverse()
    odd = (positive_value - negative_value).scale(inverse_two_x)
    return even + beta * odd


def canonical_polynomial(
    coefficients: tuple[Fp2, ...],
    max_coefficient_count: int = MAX_POLYNOMIAL_COEFFICIENTS,
) -> tuple[Fp2, ...]:
    """Validate and return one canonical bounded coefficient sequence.

    Zero is encoded as the one-element sequence ``(0,)``.  Every nonzero
    polynomial ends in a nonzero coefficient, so adding trailing zero slots
    cannot create a second syntax for the same polynomial.
    """

    if type(max_coefficient_count) is not int or not (
        1 <= max_coefficient_count <= MAX_POLYNOMIAL_COEFFICIENTS
    ):
        raise malformed(
            "field:polynomial",
            "FRI-IOR-FIELD-015",
            "the polynomial coefficient bound is outside the finite profile",
        )
    if not isinstance(coefficients, tuple) or not coefficients:
        raise malformed(
            "field:polynomial",
            "FRI-IOR-FIELD-013",
            "a polynomial is a non-empty canonical coefficient sequence",
        )
    if not all(isinstance(coefficient, Fp2) for coefficient in coefficients):
        raise malformed(
            "field:polynomial",
            "FRI-IOR-FIELD-014",
            "every polynomial coefficient must be an Fp2 element",
        )
    if len(coefficients) > max_coefficient_count:
        raise malformed(
            "field:polynomial",
            "FRI-IOR-FIELD-016",
            "the polynomial exceeds its syntactic coefficient bound",
        )
    if len(coefficients) > 1 and coefficients[-1] == Fp2.zero():
        raise malformed(
            "field:polynomial",
            "FRI-IOR-FIELD-017",
            "a canonical nonzero polynomial cannot carry trailing zero coefficients",
        )
    return coefficients


def polynomial_degree(coefficients: tuple[Fp2, ...]) -> int:
    """Return the degree of a canonical polynomial, using ``-1`` for zero."""

    canonical = canonical_polynomial(coefficients)
    return -1 if canonical == (Fp2.zero(),) else len(canonical) - 1


def evaluate_polynomial(
    coefficients: tuple[Fp2, ...],
    point: Fp,
    resources: ResourceCounter | None = None,
) -> Fp2:
    """Evaluate a canonical bounded coefficient sequence by Horner's rule.

    The abstract cost basis charges one extension-field multiplication and one
    extension-field addition for every coefficient, including the leading
    zero-accumulator step.  The full charge is reserved before evaluation, so
    deterministic limit exhaustion cannot leave a partially charged counter.
    """

    canonical = canonical_polynomial(coefficients)
    base_point = Fp2.from_base(_require_fp_operand(point))
    if resources is not None:
        if not isinstance(resources, ResourceCounter):
            raise malformed(
                "field:polynomial",
                "FRI-IOR-FIELD-018",
                "polynomial evaluation requires a ResourceCounter when metered",
            )
        resources.consume_field_operations(
            len(canonical) * POLYNOMIAL_COEFFICIENT_FIELD_OPERATIONS
        )
    result = Fp2.zero()
    for coefficient in reversed(canonical):
        result = result * base_point + coefficient
    return result


def model_failure_of(error: Exception) -> ModelFailure | None:
    """A tiny narrowing helper used by callers that expose typed results."""

    return error if isinstance(error, ModelFailure) else None
