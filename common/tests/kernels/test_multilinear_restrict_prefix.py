"""The total Math operation reaches the native Host without table-shape guards."""
from pathlib import Path

import pytest

from binary_reference import BASE, readable
from entry import Entry


@pytest.mark.parametrize('field', ['bls12-381.fr', BASE])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_total_prefix_restriction(toolchain, journal, directory, field, flags):
    fixture = Path(__file__).resolve().parents[3] / (
        'compiler/test/fixtures/structured-source/restrict_prefix.zkc')
    source = fixture.read_text().replace('bls12-381.fr', field)
    entry = Entry(toolchain, journal, directory, source, flags)
    encode = readable if field == BASE else str
    cases = [
        ('empty', [], [], []), ('empty-at-point', [], [2], []),
        ('identity', [9], [], [9]), ('singleton', [9], [2], []),
        ('odd-identity', [1, 7, 2], [], [1, 7, 2]),
        ('odd-restriction', [1, 7, 2], [2], [13]),
        ('off-cube', [1, 7, 2, 9], [2, 3], [35] if field == BASE else [27]),
        ('ordered-point', [1, 7, 2, 9], [3, 2], [38] if field == BASE else [22]),
        ('excess-point', [1, 7, 2, 9], [2, 3, 4], []),
        ('zero-one', [1, 7, 2, 9], [0, 1], [7]),
        ('one-zero', [1, 7, 2, 9], [1, 0], [2]),
    ]
    for name, values, point, expected in cases:
        assert entry.run(name, {'values': list(map(encode, values)),
                                'point': list(map(encode, point))}) == {
                                    'residual': list(map(encode, expected))}
