"""Shared FRI mathematics against independent coefficient arithmetic."""

import pytest

from coset_reference import CosetReference
from entry import Entry
from source_modules import library_modules


@pytest.mark.parametrize('field', [
    'koala-bear.ext4-binomial3', 'koala-bear.ext8-binomial3',
    'baby-bear.ext4-binomial11', 'goldilocks.ext2-binomial7',
])
@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_total_power_and_binary_fold(toolchain, journal, directory, field, flags):
    source = f'''module sample;
use fri::{{power_word, fold_value}};
use zkc::scalar as scalar;
domain F=field("{field}");
protocol Run roles(P)(base:F@P,exponent:index@P,low:F@P,high:F@P,
    beta:F@P,inverse_two:F@P,inverse_x:F@P)->(power:F@P,local_power:F@P,folded:F@P) {{
  return(power=power_word(base,exponent), local_power=scalar::power(base,exponent),
    folded=fold_value(low,high,beta,inverse_two,inverse_x));
}}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source,
                  [*library_modules('protocols/polynomial/fri'), *flags])
    ref = CosetReference(field)
    encode = ref.encode
    inverse_two = ref.embed(pow(2, -1, ref.modulus))
    base = tuple(range(2, 2 + ref.degree))
    coefficients = [tuple(i + j + 1 for j in range(ref.degree)) for i in range(7)]
    for ordinal, exponent in enumerate([0, 1, 2, 63, 64, 1 << 63, (1 << 64) - 1]):
        x = base if ordinal % 2 else ref.sub(ref.zero, base)
        beta = [ref.zero, ref.one, base][ordinal % 3]
        low = ref.horner(coefficients, x)
        high = ref.horner(coefficients, ref.sub(ref.zero, x))
        # Coefficient-level folding is independent of the two-value formula.
        square = ref.mul(x, x)
        expected = ref.add(ref.horner(coefficients[::2], square),
                           ref.mul(beta, ref.horner(coefficients[1::2], square)))
        actual = entry.run(f'word-{ordinal}', {
            'base': encode(base), 'exponent': str(exponent),
            'low': encode(low), 'high': encode(high), 'beta': encode(beta),
            'inverse_two': encode(inverse_two),
            'inverse_x': encode(ref.power(x, ref.modulus**ref.degree - 2)),
        })
        assert actual == {'power': encode(ref.power(base, exponent)),
                          'local_power': encode(ref.power(base, exponent)),
                          'folded': encode(expected)}
    for exponent in [0, (1 << 64) - 1]:
        actual = entry.run(f'zero-{exponent}', {
            'base': encode(ref.zero), 'exponent': str(exponent),
            'low': encode(ref.zero), 'high': encode(ref.zero),
            'beta': encode(base), 'inverse_two': encode(inverse_two),
            'inverse_x': encode(ref.one),
        })
        assert actual == {'power': encode(ref.one if exponent == 0 else ref.zero),
                          'local_power': encode(ref.one if exponent == 0 else ref.zero),
                          'folded': encode(ref.zero)}


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_total_word_bit_width(toolchain, journal, directory, flags):
    source = """module sample;
use zkc::indices::{bit_width};
protocol Run roles(P)(value:index@P)->(width:index@P) {
  return(width=bit_width(value));
}
entry fn Demo(inputs:Run::Inputs) { return Run::run(inputs); }
"""
    entry = Entry(toolchain, journal, directory, source,
                  [*library_modules('protocols/polynomial/fri'), *flags])
    values = set(range(256))
    for bit in range(64):
        values.update([1 << bit, (1 << bit) - 1, (1 << bit) + 1])
    values.add((1 << 64) - 1)
    for value in sorted(values):
        assert entry.run(f'width-{value}', {'value': str(value)}) == {
            'width': str(value.bit_length())}
