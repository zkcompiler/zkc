"""Integer arithmetic in KoalaBear[X]/(X^8 - 3), independent of native code."""

from binomial_reference import OCTIC, P  # noqa: F401  (re-exported modulus)

ZERO = OCTIC.ZERO
ONE = OCTIC.ONE
add = OCTIC.add
mul = OCTIC.mul
power = OCTIC.power
coordinates = OCTIC.coordinates
