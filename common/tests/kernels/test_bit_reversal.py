"""Bit-reversal permutations through source, IR and Host for every field family.

The expected order reverses binary digit strings in Python, independently of
the native word-level reversal.
"""
import pytest

from entry import Entry
from source_modules import library_modules

FIELDS = {'bls12-381.fr': 1, 'ristretto255.scalar': 1, 'bn254.fr': 1,
          'koala-bear': 1, 'koala-bear.ext8-binomial3': 8}

SOURCE = '''module sample;
use zkc::vector as vector;
use zkc::vector::{{Vector}};
domain F=field("{field}");
protocol Run roles(P)(xs:Vector<F>@P, table:Vector<F>@P, width:index@P)
  -> (elements:Vector<F>@P, rows:Vector<F>@P) {{
  let elements @P=vector::bit_reverse(xs);
  let rows @P=vector::bit_reverse_rows(table,width);
  return (elements=elements, rows=rows);
}}
run Demo=Run;
'''


def reversed_index(i, bits):
    return int(format(i, f'0{bits}b')[::-1], 2) if bits else 0


def element(degree, n):
    return str(n) if degree == 1 else [str(n)] + [str(n + j) for j in range(1, degree)]


@pytest.mark.parametrize('field', sorted(FIELDS))
def test_bit_reversal(toolchain, journal, directory, field):
    degree = FIELDS[field]
    entry = Entry(toolchain, journal, directory, SOURCE.format(field=field), library_modules('zkc'))
    for bits in (0, 1, 3, 5):
        n = 1 << bits
        xs = [element(degree, 7 + i) for i in range(n)]
        for width in (1, 3):
            table = [element(degree, 100 + i) for i in range(n * width)]
            result = entry.run(f'n{n}-w{width}', {'xs': xs, 'table': table, 'width': width})
            assert result['elements'] == [xs[reversed_index(i, bits)] for i in range(n)]
            assert result['rows'] == [table[reversed_index(r, bits) * width + c]
                                      for r in range(n) for c in range(width)]
    entry.run('odd-length', {'xs': [element(degree, 1)] * 3, 'table': [], 'width': 1},
              refuses='vector-bit-reversal')
    entry.run('odd-height', {'xs': [element(degree, 1)], 'table': [element(degree, 1)] * 6,
                             'width': 2}, refuses='vector-bit-reversal')
    entry.run('ragged-rows', {'xs': [element(degree, 1)], 'table': [element(degree, 1)] * 3,
                              'width': 2}, refuses='vector-shape')
