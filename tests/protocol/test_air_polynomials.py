"""Source AIR polynomial helpers against independent extension arithmetic."""
import json
from pathlib import Path

import pytest

from octic_reference import P, ONE, ZERO, add, mul, power, coordinates

ROOT = Path(__file__).resolve().parents[2]
LIBRARY = ROOT / 'libraries/air/polynomial.zkc'
SHIFT = [3, 1, 0, 0, 0, 0, 0, 0]
CLIENT = '''module example;
use air_polynomial::{Vector, vanishing_values, vanishing, extend_columns, transpose};
domain E = field("koala-bear.ext8-binomial3");
protocol Run roles(P)(height:index@P, begin:index@P, end:index@P, shift:E@P,
 size:index@P, x:E@P, values:Vector<E>@P, width:index@P)
 -> (scope:Vector<E>@P, at:E@P, extension:Vector<E>@P, rows:Vector<E>@P) {
 let scope@P=vanishing_values(height,begin,end,shift,size);
 let at@P=vanishing(height,begin,end,x);
 let extension@P=extend_columns(values,width,height,shift,size);
 let rows@P=transpose(extension,width,size);
 return (scope=scope,at=at,extension=extension,rows=rows);
}
entry Demo=Run;
'''


def wire(values, scalar=False):
    return (b'ZKCV\x00' + bytes([26 if scalar else 27])
            + (b'' if scalar else len(values).to_bytes(4, 'little'))
            + b''.join(coordinates(v) for v in values)).hex()


def points(size, shift=ONE):
    root = pow(1791270792, (1 << 24) // size, P)
    return [mul(shift, [pow(root, i, P)] + [0] * 7) for i in range(size)]


def evaluate(coefficients, x):
    result = ZERO
    for c in reversed(coefficients):
        result = add(c, mul(x, result))
    return result


def zero_polynomial_at(roots, x):
    result = ONE
    for root in roots:
        result = mul(result, add(x, [(-y) % P for y in root]))
    return result


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_scope_polynomials_and_column_extensions(toolchain, journal, directory, flags):
    source = directory / 'client.zkc'
    source.write_text(CLIENT)
    package = directory / 'math.entry'
    report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=example={source}', f'--module=air_polynomial={LIBRARY}',
                           '--entry=example::Demo', f'--output={package}', *flags])
    pin = report['package_sha256']
    for height, size in [(8, 32), (16, 64)]:
        subgroup = points(height)
        coset = points(size, SHIFT)
        x = [11, 3, 0, 0, 0, 0, 0, 0]
        polynomials = [[ONE, SHIFT, [9] + [0] * 7],
                       [ZERO] * (height - 1) + [[2, 1, 0, 1, 0, 0, 0, 0]]]
        columns = [evaluate(c, at) for c in polynomials for at in subgroup]
        extended = [evaluate(c, at) for c in polynomials for at in coset]
        transposed = [evaluate(c, at) for at in coset for c in polynomials]
        for begin, end in [(0, height), (0, 1), (height - 1, height),
                           (0, height - 1), (1, height - 1), (2, 5), (3, 3)]:
            inputs = {'height': height, 'begin': begin, 'end': end, 'size': size,
                      'shift': wire([SHIFT], True), 'x': wire([x], True),
                      'values': wire(columns), 'width': len(polynomials)}
            request = journal.write('inputs.json', {'format': 'zkc.entry-run/0', 'session': 'air_math',
                                                  'roles': {'P': {'inputs': inputs}}})
            output = directory / 'outputs.json'
            journal.run([toolchain.runtime, 'run', package, pin, request, f'--results={output}'])
            values = json.loads(output.read_text())['roles']['P']
            roots = subgroup[begin:end]
            assert values['scope'] == wire([zero_polynomial_at(roots, at) for at in coset])
            assert values['at'] == wire([zero_polynomial_at(roots, x)], True)
            assert values['extension'] == wire(extended)
            assert values['rows'] == wire(transposed)
            # Direct roots determine the exact polynomial, including full H.
            if begin == 0 and end == height:
                assert zero_polynomial_at(roots, x) == add(power(x, height), [P - 1] + [0] * 7)

    for change in [{'begin': 5, 'end': 2}, {'end': height + 1}, {'values': wire(columns[:-1])}]:
        request = journal.write('invalid.json', {'format': 'zkc.entry-run/0', 'session': 'air_math',
            'roles': {'P': {'inputs': inputs | change}}})
        refused = journal.json([toolchain.runtime, 'run', package, pin, request],
                               refuses='entry-run-incomplete')
        cause = refused['execution']['roles'][0]['after'][1]['cause']
        assert cause[0] == 'explicit' and cause[1]['text'] == 'reject'
