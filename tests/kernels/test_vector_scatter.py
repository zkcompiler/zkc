"""Vector scatter uses direct modular sums through the current Entry Host."""

import random

import pytest

from entry import Entry

DOMAINS = [
    ('bls12-381.fr', 52435875175126190479447740508185965837690552500527637822603658699938581184513, 66, 32),
    ('ristretto255.scalar', 2**252 + 27742317777372353535851937790883648493, 14, 32),
    ('koala-bear', 2130706433, 20, 4),
]


def wire(values, tag, width):
    return (b'ZKCV\x00' + bytes([tag]) + len(values).to_bytes(4, 'little')
            + b''.join(x.to_bytes(width, 'little') for x in values)).hex()


@pytest.mark.parametrize('domain,modulus,tag,width', DOMAINS)
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_duplicate_indices_accumulate_and_zero_slots_survive(toolchain, journal, directory,
                                                            domain, modulus, tag, width, flags):
    source = f'''module sample;
domain F = field("{domain}");
type Vector<E:Field> = builtin("vector", E);
fn scatter(xs:Vector<F>) -> Vector<F> {{
  return kernel<F>("vector.scatter_sum", xs; "5", "3", "1", "3", "1", "4");
}}
protocol Run roles(P)(xs:Vector<F>@P) -> (result:Vector<F>@P) {{
  let result @P = scatter(xs);
  return (result=result);
}}
entry Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    rng = random.Random(718)
    cases = [[0] * 5, [modulus - 1, 2, 3, modulus - 1, 0]]
    cases += [[rng.randrange(modulus) for _ in range(5)] for _ in range(5)]
    for number, values in enumerate(cases):
        expected = [0, (values[1] + values[3]) % modulus, 0,
                    (values[0] + values[2]) % modulus, values[4]]
        assert entry.run(f'case{number}', {'xs': wire(values, tag, width)})['result'] == wire(expected, tag, width)
    entry.run('wrong-length', {'xs': wire([1, 2], tag, width)}, refuses='entry-run-incomplete')
    entry.run('truncated-wire', {'xs': wire([1] * 5, tag, width)[:-2]}, refuses=True)
