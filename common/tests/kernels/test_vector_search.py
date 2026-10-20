"""Ordered search through the authored vector contract and common Host."""
import pytest

from entry import Entry
from source_modules import core_packages, library_modules
from binary_reference import BASE, CUBIC, readable

FIELDS = {'bls12-381.fr': 1, 'bn254.fr': 1, 'ristretto255.scalar': 1,
          'koala-bear': 1, 'koala-bear.ext4-binomial3': 4,
          'koala-bear.ext8-binomial3': 8, BASE: 1, CUBIC: 3}


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_search_preserves_last_match_absence_and_aliases(toolchain, journal, directory, field, flags):
    source = f'''module sample;
use zkc::vector as v;
use zkc::vector::{{Vector}};
domain F=field("{field}");
protocol Run roles(P)(xs:Vector<F>@P,needle:F@P)
    ->(position:index@P,again:index@P,unchanged:Vector<F>@P) {{
  let position=v::find_last(xs,needle);
  let again=v::find_last(xs,needle);
  return(position=position,again=again,unchanged=xs);
}}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source,
                  [*library_modules(*core_packages()), *flags])
    degree = FIELDS[field]
    def encode(n):
        if field in (BASE, CUBIC):
            return readable(n if degree == 1 else [n+j for j in range(degree)])
        return str(n) if degree == 1 else [str(n)] + [str(n+j) for j in range(1, degree)]
    for label, ns, needle in [('empty', [], 3), ('singleton', [3], 3),
                             ('absent', [3, 7, 11], 5), ('first', [3, 7, 11], 3),
                             ('last', [3, 7, 11], 11), ('duplicate', [3, 7, 3, 11], 3)]:
        xs, value = list(map(encode, ns)), encode(needle)
        position = max((i for i, x in enumerate(xs) if x == value), default=len(xs))
        result = entry.run(label, {'xs': xs, 'needle': value})
        assert result == {'position': str(position), 'again': str(position), 'unchanged': xs}
    if degree > 1:
        value = encode(3)
        altered = value.copy()
        altered[-1] = hex(int(altered[-1], 16)+1) if field == CUBIC else str(int(altered[-1])+1)
        assert entry.run('higher-coordinate', {'xs': [value, altered], 'needle': value})['position'] == '0'
