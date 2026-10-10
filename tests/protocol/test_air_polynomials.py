"""Source AIR polynomial helpers against independent extension arithmetic."""

from input_files import input_files
import json
from pathlib import Path

import pytest

from octic_reference import P, ONE, ZERO, add, mul, power

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
run Demo=Run;
'''


def wire(values, scalar=False):
    rows = [[str(w) for w in v] for v in values]
    return rows[0] if scalar else rows


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


SCOPE_CLIENT = '''module example;
use air_polynomial::{Vector, vanishing_values, vanishing, empty, append, length, get};
domain E = field("koala-bear.ext8-binomial3");
protocol Run roles(P)(height:index@P, begin:index@P, end:index@P, shift:E@P,
 size:index@P, samples:Vector<E>@P) -> (scope:Vector<E>@P, sampled:Vector<E>@P) {
 let scope@P=vanishing_values(height,begin,end,shift,size);
 let sampled@P=sample(height,begin,end,samples);
 return (scope=scope,sampled=sampled);
}
fn sample(height:index,begin:index,end:index,samples:Vector<E>) -> Vector<E> {
 let mut results=empty<E>();
 for i in 0..length(samples) {
  results=append(results,vanishing(height,begin,end,get(samples,i)));
 }
 return results;
}
run Demo=Run;
'''


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_scope_polynomials_on_intersecting_cosets(toolchain, journal, directory, flags):
    source = directory / 'scope.zkc'
    source.write_text(SCOPE_CLIENT)
    package = directory / 'scope.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=example={source}', f'--module=air_polynomial={LIBRARY}',
                           'example::Demo', f'--output={package}', *flags])
    height = 8
    subgroup = points(height)
    samples = subgroup + [ZERO, SHIFT]
    # Equal, smaller, larger and shifted intersecting domains, plus a disjoint
    # control. Scalar samples include every active and every complement root.
    for size, shift in [(4, ONE), (8, ONE), (16, ONE), (4, subgroup[1]), (16, SHIFT)]:
        coset = points(size, shift)
        for begin, end in [(0, 7), (1, 8), (1, 7), (0, 8), (3, 3), (2, 5)]:
            inputs = {'height': height, 'begin': begin, 'end': end, 'size': size,
                      'shift': wire([shift], True), 'samples': wire(samples)}
            request = input_files(journal, 'inputs.json', session='scope_roots', roles={'P': {'inputs': inputs}})
            output = directory / 'outputs.json'
            journal.run([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={report['package_sha256']}', *request, f'--results={output}'])
            actual = json.loads(output.read_text())['roles']['P']
            roots = subgroup[begin:end]
            assert actual['scope'] == wire([zero_polynomial_at(roots, at) for at in coset])
            assert actual['sampled'] == wire([zero_polynomial_at(roots, at) for at in samples])


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_scope_polynomials_and_column_extensions(toolchain, journal, directory, flags):
    source = directory / 'client.zkc'
    source.write_text(CLIENT)
    package = directory / 'math.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=example={source}', f'--module=air_polynomial={LIBRARY}',
                           'example::Demo', f'--output={package}', *flags])
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
            request = input_files(journal, 'inputs.json', session='air_math', roles={'P': {'inputs': inputs}})
            output = directory / 'outputs.json'
            journal.run([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', *request, f'--results={output}'])
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
        request = input_files(journal, 'invalid.json', session='air_math', roles={'P': {'inputs': inputs | change}})
        refused = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', *request],
                               refuses='entry-run-incomplete')
        cause = refused['execution']['roles'][0]['after'][1]['cause']
        assert cause[0] == 'explicit' and cause[1]['text'] == 'reject'
