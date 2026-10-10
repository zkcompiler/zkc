"""Checked native maps apply scalar math helpers to whole vectors.

Every case compiles source through the common compiler and runs the package
through the ordinary Entry Host. Expected values are computed here, row by row,
independently of the compiler's bulk realization.
"""

from input_files import input_files
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
run Demo = Run;
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
run Demo = Run;
'''

# A map inside a loop executes, and checks shapes, once per iteration.
LOOP = '''module sample;
domain Fr = field("koala-bear");
type Vector<F: Field> = builtin("vector", F);
math fn affine<F: Field>(low: F, high: F, r: F) -> F {
  return low + (high - low) * r;
}
fn repeat(a: Vector<Fr>, b: Vector<Fr>, s: Fr, n: index) -> Vector<Fr> {
  let mut acc = a;
  for _ in 0..n {
    acc = map affine(each acc, each b, s);
  }
  return acc;
}
protocol Run roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, s: Fr @P, n: index @P)
    -> (repeated: Vector<Fr> @P) {
  let repeated = repeat(a, b, s, n);
  return (repeated = repeated);
}
run Demo = Run;
'''

# One helper realized for a scalar call and for two different row masks.
SHARED = '''module sample;
domain Fr = field("koala-bear");
type Vector<F: Field> = builtin("vector", F);
math fn affine<F: Field>(low: F, high: F, r: F) -> F {
  return low + (high - low) * r;
}
fn pairwise(a: Vector<Fr>, b: Vector<Fr>, s: Fr) -> Vector<Fr> {
  return map affine(each a, each b, s);
}
fn towards(a: Vector<Fr>, y: Fr, s: Fr) -> Vector<Fr> {
  return map affine(each a, y, s);
}
fn single(x: Fr, y: Fr, s: Fr) -> Fr { return affine(x, y, s); }
protocol Run roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, x: Fr @P, y: Fr @P,
                      s: Fr @P)
    -> (rows: Vector<Fr> @P, toward: Vector<Fr> @P, scalar: Fr @P) {
  let rows = pairwise(a, b, s);
  let toward = towards(a, y, s);
  let scalar = single(x, y, s);
  return (rows = rows, toward = toward, scalar = scalar);
}
run Demo = Run;
'''


def affine(low, high, r):
    return (low + (high - low) * r) % MODULUS


def vector(values, extension=False):
    return [[str(v)] + ["0"] * 7 for v in values] if extension else [str(v) for v in values]


def scalar(value):
    return str(value)


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
    request = input_files(entry.journal, name, roles={'P': {'inputs': values}})
    output = entry.directory / f'{name}.outputs.json'
    return entry.journal.json([entry.tools.runtime, 'run', f'--package={entry.package}', f'--sha256={entry.pin}', *request, f'--results={output}'])


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


# The Host observes only the refusal; the compiler test pins guard order.
def test_map_refuses_any_rowwise_length_mismatch(toolchain, journal, directory):
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


@pytest.mark.parametrize('flags', [[], ['--release-storage']])
def test_map_in_a_loop(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, LOOP, flags)
    rng = random.Random(9151)
    for height in (0, 3):
        a, b = ([rng.randrange(MODULUS) for _ in range(height)] for _ in range(2))
        s = rng.randrange(MODULUS)
        for rounds in (0, 1, 4):
            acc = a
            for _ in range(rounds):
                acc = [affine(x, y, s) for x, y in zip(acc, b)]
            values = {'a': vector(a), 'b': vector(b), 's': scalar(s), 'n': rounds}
            result = entry.run(f'height{height}-rounds{rounds}', values)
            assert result == {'repeated': vector(acc)}
    # Without an iteration no map executes, so unequal lengths are not read.
    values = {'a': vector([1, 2]), 'b': vector([3]), 's': scalar(5), 'n': 0}
    assert entry.run('mismatch-unread', values) == {'repeated': vector([1, 2])}
    values['n'] = 2
    refused = entry.run('mismatch', values, refuses='entry-run-incomplete')
    assert 'rejected:require' in json.dumps(refused)


def test_one_helper_as_scalar_and_under_two_masks(toolchain, journal, directory):
    entry = Entry(toolchain, journal, directory, SHARED)
    rng = random.Random(2203)
    a, b = ([rng.randrange(MODULUS) for _ in range(5)] for _ in range(2))
    x, y, s = (rng.randrange(MODULUS) for _ in range(3))
    values = {'a': vector(a), 'b': vector(b), 'x': scalar(x), 'y': scalar(y), 's': scalar(s)}
    assert entry.run('shared', values) == {
        'rows': vector([affine(p, q, s) for p, q in zip(a, b)]),
        'toward': vector([affine(p, y, s) for p in a]),
        'scalar': scalar(affine(x, y, s))}


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
    package = directory / f'{entry}.zkpkg'
    result = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                           f'--project={PROJECT}/zkc.toml',
                           f'example::{entry}', f'--output={package}'])
    return package, result['package_sha256']


def run(toolchain, journal, directory, package, pin, name, roles, refuses=None):
    request = input_files(journal, f'{name}.json', session='native_map_example', roles=roles)
    output = directory / f'{name}.outputs.json'
    result = journal.json([toolchain.runtime, 'run', f'--package={package}', f'--sha256={pin}', *request, f'--results={output}'], refuses=refuses)
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


# The map realizer applies three simplifications of its own: it inlines the
# helpers a formula calls, keeps subformulas over scalar inputs scalar, and
# drops scalar operations that never reach the result. The participant
# simplifier never touches a realized local body, so every variant below is
# compared with and without `--no-simplify` as well. Each variant computes the
# same rows from the same inputs; the comparisons are of the executed work.
VARIANTS = {
    # One map; `square` is inlined and `s + 1` is one scalar operation.
    'fused': '''fn combine(a: Vector<Fr>, b: Vector<Fr>, c: Vector<Fr>, s: Fr) -> Vector<Fr> {
  return map residual(each a, each b, each c, s);
}''',
    # Two maps: the helper's rows are materialized and mapped again.
    'split': '''fn combine(a: Vector<Fr>, b: Vector<Fr>, c: Vector<Fr>, s: Fr) -> Vector<Fr> {
  let squares = map square(each a);
  return map residual_of_square(each squares, each b, each c, s);
}''',
    # The scalar is supplied as a column, so `s + 1` is computed on every row.
    # The column is a fourth rowwise operand: this form also builds the column
    # and checks its length, so its measurements include that extra check.
    'rows': '''fn combine(a: Vector<Fr>, b: Vector<Fr>, c: Vector<Fr>, s: Fr) -> Vector<Fr> {
  let column = kernel<Fr>("vector.fill", s, kernel<Fr>("vector.length", a));
  return map residual(each a, each b, each c, each column);
}''',
    # A scalar product that never reaches the result.
    'dead': '''fn combine(a: Vector<Fr>, b: Vector<Fr>, c: Vector<Fr>, s: Fr) -> Vector<Fr> {
  return map residual_dead(each a, each b, each c, s);
}''',
}

PRELUDE = '''module sample;
domain Fr = field("koala-bear");
type Vector<F: Field> = builtin("vector", F);
math fn square<F: Field>(x: F) -> F { return x * x; }
math fn residual<F: Field>(a: F, b: F, unused: F, s: F) -> F {
  return (s + 1) * (square(a) - b) + s;
}
math fn residual_of_square<F: Field>(sq: F, b: F, unused: F, s: F) -> F {
  return (s + 1) * (sq - b) + s;
}
math fn residual_dead<F: Field>(a: F, b: F, unused: F, s: F) -> F {
  let dead = s * s;
  return (s + 1) * (square(a) - b) + s;
}
'''

PROTOCOL = '''
protocol Run roles(P)(a: Vector<Fr> @P, b: Vector<Fr> @P, c: Vector<Fr> @P, s: Fr @P)
    -> (combined: Vector<Fr> @P) {
  let combined = combine(a, b, c, s);
  return (combined = combined);
}
run Demo = Run;
'''


def realized_operation_counts(toolchain, journal, directory, name, source):
    """Operations in the helper formula and in the realized map body.

    The emitted original keeps every helper operation, used or not; the
    prepared module holds the realized `local.func` the checker admitted.
    """
    path = directory / f'{name}.zkc'
    path.write_text(source)
    emitted = journal.run([toolchain.compiler, 'language-emit', '--source-format=zkc',
                           '--entry=sample::Demo', f'--module=sample={path}'])
    original = directory / f'{name}.mlir'
    original.write_text(emitted)
    prepared = journal.run([toolchain.optimizer, '--zkc-prepare-protocol', str(original)])
    helper = sum(line.count('algebra.field_') + line.count('algebra.constant')
                 for line in emitted.splitlines())
    body, inside = 0, False
    for line in prepared.splitlines():
        if 'local.func @zkl_map_' in line:
            inside = True
        elif inside and line.strip().startswith('return'):
            inside = False
        elif inside and ('algebra.exec.' in line or 'local.exec.' in line):
            body += 1
    return helper, body


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_realizer_simplifications_change_work_not_values_or_checks(toolchain, journal, directory, flags):
    rng = random.Random(9043)
    height = 256
    a, b, c = ([rng.randrange(MODULUS) for _ in range(height)] for _ in range(3))
    s = rng.randrange(MODULUS)
    expected_rows = [((s + 1) * (x * x - y) + s) % MODULUS for x, y in zip(a, b)]
    usage, values = {}, {}
    for name, combine in VARIANTS.items():
        entry = Entry(toolchain, journal, subdirectory(directory, name),
                      PRELUDE + combine + PROTOCOL, flags)
        result = report(entry, 'rows', inputs(a, b, c, s))
        assert result['status'] == 'executed'
        usage[name] = result['execution']['roles'][0]['usage']
        values[name] = entry.run('values', inputs(a, b, c, s))['combined']
        # Every variant still compares the unread column before any arithmetic,
        # with or without its own simplification.
        refused = entry.run('unread-mismatch', inputs(a, b, c[:-1], s),
                            refuses='entry-run-incomplete')
        assert 'rejected:require' in json.dumps(refused), name
    assert all(value == vector(expected_rows) for value in values.values())
    fused, split, rows, dead = (usage[name] for name in ('fused', 'split', 'rows', 'dead'))
    # Inlining the helper saves the intermediate column and its own shape check.
    assert fused['instructions'] < split['instructions']
    assert fused['total_value_bytes'] < split['total_value_bytes']
    assert fused['logical_bytes'] < split['logical_bytes']
    # Keeping `s + 1` scalar saves one column of work and one broadcast; the
    # column form additionally builds and length-checks its fourth operand, so
    # this difference measures hoisting together with that extra check.
    assert fused['instructions'] < rows['instructions']
    assert fused['logical_bytes'] < rows['logical_bytes']
    # The dead product leaves no trace in the executed work.
    assert dead == fused


def test_realizer_simplifications_are_visible_in_the_realized_body(toolchain, journal, directory):
    counts = {name: realized_operation_counts(toolchain, journal, directory, name,
                                              PRELUDE + combine + PROTOCOL)
              for name, combine in VARIANTS.items()}
    # The dead helper has one more formula operation and the same realized body.
    assert counts['dead'][0] == counts['fused'][0] + 1
    assert counts['dead'][1] == counts['fused'][1]
    # Fusion realizes one body; the split form realizes two maps and the
    # helper's own shape check, so it needs more operations overall. The
    # prepared module counts both bodies here.
    assert counts['split'][1] > counts['fused'][1]
    # Supplying the scalar as a column costs a fourth length check with its
    # comparison and broadcasts instead of scalar arithmetic; the count again
    # measures both together.
    assert counts['rows'][1] > counts['fused'][1]
