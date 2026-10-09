"""Checked native maps apply scalar math helpers to whole vectors.

Every case compiles source through the common compiler and runs the package
through the ordinary Entry Host. Expected values are computed here, row by row,
independently of the compiler's bulk realization.
"""
import json
import random
from pathlib import Path

import pytest

from entry import Entry

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / 'examples/projects/native-map'
MODULUS = 2130706433  # KoalaBear

SOURCE = '''module sample;
domain Fr = field("koala-bear");
type Vector<F: Field> = builtin("vector", F);
math fn square<F: Field>(x: F) -> F { return x * x; }
math fn affine<F: Field>(low: F, high: F, r: F) -> F {
  return low + (high - low) * r;
}
math fn residual<F: Field>(a: F, b: F, unused: F, s: F) -> F {
  return (s + 1) * (square(a) - b) + s;
}
math fn shifted<F: Field>(x: F, s: F) -> F { return s + 1; }
fn fold<F: Field>(low: Vector<F>, high: Vector<F>, r: F) -> Vector<F> {
  return map affine(each low, each high, r);
}
fn combine(a: Vector<Fr>, b: Vector<Fr>, c: Vector<Fr>, s: Fr) -> Vector<Fr> {
  return map residual<Fr>(each a, each b, each c, s);
}
fn broadcast(a: Vector<Fr>, s: Fr) -> Vector<Fr> {
  return map shifted(each a, s);
}
protocol Run roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, c: Vector<Fr> @P,
                      s: Fr @P)
    -> (folded: Vector<Fr> @P, combined: Vector<Fr> @P,
        constant: Vector<Fr> @P) {
  let folded = fold(a, b, s);
  let combined = combine(a, b, c, s);
  let constant = broadcast(a, s);
  return (folded = folded, combined = combined, constant = constant);
}
entry Demo = Run;
'''

# The mapped result is never used; its shape checks still execute.
DEAD = '''module sample;
domain Fr = field("koala-bear");
type Vector<F: Field> = builtin("vector", F);
math fn affine<F: Field>(low: F, high: F, r: F) -> F {
  return low + (high - low) * r;
}
fn dead(a: Vector<Fr>, b: Vector<Fr>, s: Fr) -> Vector<Fr> {
  let unused = map affine(each a, each b, s);
  return a;
}
protocol Run roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, s: Fr @P)
    -> (kept: Vector<Fr> @P) {
  let kept = dead(a, b, s);
  return (kept = kept);
}
entry Demo = Run;
'''


def vector(values, extension=False):
    width, tag = (32, 27) if extension else (4, 20)
    return (b'ZKCV\x00' + bytes([tag]) + len(values).to_bytes(4, 'little')
            + b''.join(v.to_bytes(4, 'little').ljust(width, b'\x00') for v in values)).hex()


def scalar(value):
    return (b'ZKCV\x00\x13' + value.to_bytes(4, 'little')).hex()


def expected(a, b, c, s):
    del c  # The residual formula ignores its third input.
    folded = [(x + (y - x) * s) % MODULUS for x, y in zip(a, b)]
    combined = [((s + 1) * (x * x - y) + s) % MODULUS for x, y in zip(a, b)]
    constant = [(s + 1) % MODULUS for _ in a]
    return {'folded': vector(folded), 'combined': vector(combined),
            'constant': vector(constant)}


def inputs(a, b, c, s):
    return {'a': vector(a), 'b': vector(b), 'c': vector(c), 's': scalar(s)}


def subdirectory(directory, name):
    path = directory / name
    path.mkdir()
    return path


def report(entry, name, values):
    request = entry.journal.write(f'{name}.inputs.json', {
        'format': 'zkc.entry-run/0', 'session': 'map_controls',
        'roles': {'P': {'inputs': values}}})
    output = entry.directory / f'{name}.outputs.json'
    return entry.journal.json([entry.tools.runtime, 'run', entry.package, entry.pin,
                               request, f'--results={output}'])


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_map_values_broadcasts_and_empty_vectors(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, SOURCE, flags)
    rng = random.Random(4127)
    for height in (0, 1, 3, 17):
        a, b, c = ([rng.randrange(MODULUS) for _ in range(height)] for _ in range(3))
        s = rng.randrange(MODULUS)
        result = entry.run(f'height{height}', inputs(a, b, c, s))
        assert result == expected(a, b, c, s)
    edge = [0, 1, MODULUS - 1]
    assert entry.run('edges', inputs(edge, edge[::-1], edge, MODULUS - 1)) == \
        expected(edge, edge[::-1], edge, MODULUS - 1)


def test_map_checks_every_rowwise_shape_before_arithmetic(toolchain, journal, directory):
    entry = Entry(toolchain, journal, directory, SOURCE)
    good = [1, 2, 3]
    for name, values in [('used', inputs(good, [4, 5], good, 2)),
                         ('unused', inputs(good, good, [7, 8], 2)),
                         ('empty-against-rows', inputs([], good, good, 2))]:
        refused = entry.run(name, values, refuses='entry-run-incomplete')
        assert 'rejected:require' in json.dumps(refused), name


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_unused_map_result_still_checks_shapes(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, DEAD, flags)
    values = {'a': vector([1, 2]), 'b': vector([3, 4]), 's': scalar(5)}
    assert entry.run('equal', values)['kept'] == vector([1, 2])
    values['b'] = vector([3])
    refused = entry.run('mismatch', values, refuses='entry-run-incomplete')
    assert 'rejected:require' in json.dumps(refused)


def test_artifact_and_work_are_independent_of_height(toolchain, journal, directory):
    first = Entry(toolchain, journal, subdirectory(directory, 'first'), SOURCE)
    second = Entry(toolchain, journal, subdirectory(directory, 'second'), SOURCE)
    assert first.pin == second.pin
    assert first.package.read_bytes() == second.package.read_bytes()
    instructions = set()
    for height in (1, 8, 256):
        rows = list(range(height))
        result = report(first, f'height{height}', inputs(rows, rows, rows, 3))
        assert result['status'] == 'executed'
        instructions.add(result['execution']['roles'][0]['usage']['instructions'])
    # One executed instruction sequence for every height: no per-row expansion.
    assert len(instructions) == 1


def build(toolchain, journal, directory, entry):
    package = directory / f'{entry}.entry'
    result = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                           f'--module=example={PROJECT}/main.zkc',
                           f'--entry=example::{entry}', f'--output={package}'])
    return package, result['package_sha256']


def run(toolchain, journal, directory, package, pin, name, roles, refuses=None):
    request = journal.write(f'{name}.json', {'format': 'zkc.entry-run/0',
                                             'session': 'native_map_example', 'roles': roles})
    output = directory / f'{name}.outputs.json'
    result = journal.json([toolchain.runtime, 'run', package, pin, request,
                           f'--results={output}'], refuses=refuses)
    return result if refuses else json.loads(output.read_text())['roles']


def test_native_map_example_gates(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'Check')
    selector, left, right = [1, 0, 1, 0], [3, 4, 5, MODULUS - 1], [7, 8, 9, 2]
    output = [(x * y if t else x + y) % MODULUS for t, x, y in zip(selector, left, right)]

    def columns(out, sel=selector):
        return {'V': {'inputs': {'selector': vector(sel), 'left': vector(left),
                                 'right': vector(right), 'output': vector(out)}}}
    assert run(toolchain, journal, directory, package, pin, 'valid', columns(output))['V']['accepted'] is True
    changed = output[:2] + [(output[2] + 1) % MODULUS] + output[3:]
    assert run(toolchain, journal, directory, package, pin, 'changed', columns(changed))['V']['accepted'] is False
    run(toolchain, journal, directory, package, pin, 'short', columns(output[:3]),
        refuses='entry-run-incomplete')


def test_native_map_example_combination(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, 'Interactive')

    def roles(left, right):
        values = {'left': vector(left, True), 'right': vector(right, True)}
        return {'P': {'inputs': values}, 'V': {'inputs': values}}
    result = run(toolchain, journal, directory, package, pin, 'valid', roles([1, 2, 3], [4, 5, 6]))
    assert result['V']['accepted'] is True
    run(toolchain, journal, directory, package, pin, 'short', roles([1, 2, 3], [4, 5]),
        refuses='entry-run-incomplete')
