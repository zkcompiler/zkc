"""Total ui64 mathematics through the public library, compiler and native Host."""

from source_modules import core_packages, library_modules

import pytest

from entry import Entry

MODULES = library_modules(*core_packages())
MODULUS = 1 << 64
MAXIMUM = MODULUS - 1
SOURCE = '''module sample;
use zkc::indices as indices;
math fn words(a:index,b:index,n:index,choose:bool)->(index,index,index,index,index,index,index) {
  let sum=indices::wrapping_add(a,b);
  let difference=indices::wrapping_sub(a,b);
  let bits=indices::bit_and(a,b);
  let shifted=indices::logical_shift_right(a,b);
  let half=indices::logical_shift_right(n,1);
  let low=indices::bit_and(a,indices::wrapping_sub(half,1));
  let high=indices::wrapping_add(low,half);
  let selected=if choose { low } else { high };
  return(sum,difference,bits,shifted,low,high,selected);
}
protocol Run roles(P)(a:index@P,b:index@P,n:index@P,choose:bool@P)
  ->(result:(index,index,index,index,index,index,index)@P) {
  return words(a,b,n,choose);
}
entry fn Demo(inputs:Run::Inputs) { return Run::run(inputs); }
'''


def reference(a, b, n, choose):
    half = n // 2
    low = a & ((half - 1) % MODULUS)
    high = (low + half) % MODULUS
    return [(a + b) % MODULUS, (a - b) % MODULUS, a & b,
            a // (1 << b) if b < 64 else 0, low, high,
            low if choose else high]


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_total_words_and_composed_maps_on_all_input_boundaries(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, SOURCE, [*MODULES, *flags])
    cases = {(a, shift, 0) for a in [0, 1, MAXIMUM] for shift in [0, 1, 63, 64, MAXIMUM]}
    for n in [0, 1, 2, 3, 6, 7, 8, 1 << 63, MAXIMUM - 1, MAXIMUM]:
        cases.update((a, 1, n) for a in [0, max(0, n - 1), MAXIMUM])
    for n in [2, 4, 8]:
        cases.update((a, 1, n) for a in range(n))
    for ordinal, (a, b, n) in enumerate(sorted(cases)):
        choose = ordinal % 2 == 0
        actual = entry.run(f'word-{ordinal}', {'a': str(a), 'b': str(b), 'n': str(n), 'choose': choose})
        expected = reference(a, b, n, choose)
        assert actual['result'] == [str(value) for value in expected]
        if n >= 2 and n.bit_count() == 1:
            assert expected[4:6] == [a % (n // 2), a % (n // 2) + n // 2]
        if n < 2:
            assert expected[4:6] == [a, a]


@pytest.mark.parametrize(('operation', 'left', 'right', 'diagnostic'), [
    ('index.add', MAXIMUM, 1, 'index-overflow'),
    ('index.sub', 0, 1, 'index-underflow'),
    ('index.div', 1, 0, 'index-zero-divisor'),
    ('index.mod', 1, 0, 'index-zero-divisor'),
])
def test_checked_operations_keep_their_ordered_failures(toolchain, journal, directory, operation, left, right, diagnostic):
    source = f'''module sample;
fn checked(a:index,b:index)->index=primitive("{operation}");
protocol Run roles(P)(a:index@P,b:index@P)->(result:index@P){{return checked(a,b);}}
entry fn Demo(inputs:Run::Inputs) {{return Run::run(inputs);}}
'''
    entry = Entry(toolchain, journal, directory, source)
    report = entry.run('checked', {'a': str(left), 'b': str(right)}, refuses='entry-host-run-failed')
    assert diagnostic in str(report)
