"""Ordinary and finite Views through layout source, native lowering and Host execution."""
import hashlib
import itertools
import json
from pathlib import Path

import pytest

from entry import joint_execution, joint_package
from input_files import invocation_file

SOURCE = Path(__file__).resolve().parents[3] / 'compiler/test/fixtures/layout/finite-views.zkc'
PREFIX = SOURCE.read_text().split('view def relay', 1)[0]
FLAGS = [(), ('--no-simplify',), ('--no-finite-bulk',)]
ORDINARY_MEMBERS = '''
interface Forward<A: Type + Copy + Drop>:
    view def pick<B: Type + Copy + Drop, N: nat>(value: B, other: B, padding: [A; N]) -> B
module First<K: nat, A: Type + Copy + Drop>: Forward<A>:
    view def pick<C: Type + Copy + Drop, M: nat>(value: C, other: C, padding: [A; M]) -> C:
        return value
module Second<K: nat, A: Type + Copy + Drop>: Forward<A>:
    view def pick<C: Type + Copy + Drop, M: nat>(value: C, other: C, padding: [A; M]) -> C:
        return other
type Finite<I: Type + Copy + Drop> = builtin("finite", I)
view def range(lo: index, hi: index) -> Finite<index> = domain("range")
local def ordered<I: Type + Copy + Drop, S: Type + Copy + Drop>(rows: Finite<I>, initial: S, step: local fn(S, item: I) -> S effects(stop) where item_from(item, rows)) -> S effects(stop) = finite("local.fold")
def apply(value: bool, body: fn(bool) -> bool) -> bool:
    return body(value)
def mathematical<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool:
    return M::pick<bool, 2>(x, y, padding)
local def local_total<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool effects():
    return M::pick<bool, 2>(x, y, padding)
def mathematical_scoped<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool:
    return apply(x, fn(item) => M::pick<bool, 2>(item, y, padding))
local def local_scoped<M: Forward<index>>(x: bool, y: bool, padding: [index; 2]) -> bool effects(stop):
    result <- ordered(range(index<0>(), index<1>()), x, fn(state, item) => M::pick<bool, 2>(state, y, padding))
    return result
'''


def compile_view(toolchain, journal, directory, source, flags):
    path = directory / 'views.zkc'
    path.write_text(source)
    encoded = journal.run([toolchain.compiler, 'language-package',
                           '--source-format=zkc-layout', '--entry=m::Demo',
                           f'--module=m={path}', *flags])
    package = directory / 'views.zkpkg'
    package.write_text(encoded)
    return package, hashlib.sha256(package.read_bytes()).hexdigest()


def run_view(toolchain, journal, directory, package, pin, label, values, refuses=None):
    inputs = journal.write(f'{label}.inputs.json', {'inputs': {'P': values}})
    binding = invocation_file(journal, f'{label}.invocations.json', package)
    output = directory / f'{label}.outputs.json'
    report = journal.json([toolchain.runtime, '--json', 'run',
                           f'--package={package}', f'--sha256={pin}',
                           f'--input={inputs}', binding, f'--results={output}'],
                          refuses=refuses)
    if refuses:
        return report
    assert report['status'] == 'executed'
    return json.loads(output.read_text())['value']['P']['result']


@pytest.mark.parametrize('flags', FLAGS)
def test_shared_forwarded_view_reaches_math_and_local(toolchain, journal, directory, flags):
    package, pin = compile_view(toolchain, journal, directory, SOURCE.read_text(), flags)
    original = joint_package(json.loads(package.read_text()))['original']
    for operation in ('data.domain_elements', 'data.domain_zip', 'data.finite_fold', 'exec.fold'):
        assert f'"{operation}"' in original
    assert run_view(toolchain, journal, directory, package, pin, 'empty',
                    {'xs': [], 'initial': '7'}) == '14'
    assert run_view(toolchain, journal, directory, package, pin, 'nonempty',
                    {'xs': ['2', '3'], 'initial': '1'}) == '22'


@pytest.mark.parametrize('flags', FLAGS)
def test_unused_invalid_constructor_survives_zero_product(toolchain, journal, directory, flags):
    source = PREFIX + '''
view def retained(xs: Vector<F>, ys: Vector<F>, lo: index, hi: index) -> Finite<(index, F)>:
    shared = elements(xs)
    unused = zip(shared, elements(ys))
    return product(range(lo, hi), shared)
view def forwarded(rows: Finite<(index, F)>) -> Finite<(index, F)>:
    return rows
pub protocol Demo roles(P)(xs: Vector<F> @P, ys: Vector<F> @P, lo: index @P, hi: index @P, initial: F @P) -> F @P:
    result <- ordered(forwarded(retained(xs, ys, lo, hi)), initial, fn(state, item) => state + item.1)
    return result
'''
    package, pin = compile_view(toolchain, journal, directory, source, flags)
    assert run_view(toolchain, journal, directory, package, pin, 'empty',
                    {'xs': ['2'], 'ys': ['3'], 'lo': '0', 'hi': '0', 'initial': '7'}) == '7'
    assert run_view(toolchain, journal, directory, package, pin, 'product',
                    {'xs': ['2'], 'ys': ['3'], 'lo': '0', 'hi': '2', 'initial': '7'}) == '11'
    assert run_view(toolchain, journal, directory, package, pin, 'reversed-empty-range',
                    {'xs': [], 'ys': [], 'lo': '1', 'hi': '0', 'initial': '7'}) == '7'
    refused = run_view(toolchain, journal, directory, package, pin, 'zero-product-bad-unused-zip',
                       {'xs': ['2'], 'ys': [], 'lo': '0', 'hi': '0', 'initial': '7'},
                       refuses='entry-host-run-failed')
    assert joint_execution(refused)['roles'][0]['after'][0] == 'stopped'


@pytest.mark.parametrize('flags', FLAGS)
def test_repeated_consumers_keep_distinct_admission_occurrences(toolchain, journal, directory, flags):
    source = PREFIX + '''
view def paired(xs: Vector<F>, ys: Vector<F>) -> Finite<(F, F)>:
    return zip(elements(xs), elements(ys))
local def twice(rows: Finite<(F, F)>, initial: F) -> F effects(stop):
    first <- ordered(rows, initial, fn(state, item) => state + item.0 + item.1)
    second <- ordered(rows, first, fn(state, item) => state + item.0 + item.1)
    return second
pub protocol Demo roles(P)(xs: Vector<F> @P, ys: Vector<F> @P, initial: F @P) -> F @P:
    result <- twice(paired(xs, ys), initial)
    return result
'''
    package, pin = compile_view(toolchain, journal, directory, source, flags)
    original = joint_package(json.loads(package.read_text()))['original']
    assert original.count('"exec.fold"') == 2
    assert run_view(toolchain, journal, directory, package, pin, 'empty',
                    {'xs': [], 'ys': [], 'initial': '7'}) == '7'
    assert run_view(toolchain, journal, directory, package, pin, 'repeated',
                    {'xs': ['2', '3'], 'ys': ['5', '7'], 'initial': '1'}) == '35'
    run_view(toolchain, journal, directory, package, pin, 'mismatch',
             {'xs': ['2'], 'ys': [], 'initial': '1'}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('flags', FLAGS)
@pytest.mark.parametrize('inferred', [False, True])
def test_ordinary_view_calls_from_local_and_finite_callbacks(
        toolchain, journal, directory, flags, inferred):
    result_type = '' if inferred else ' -> E'
    source = PREFIX + f'''
view def pick<E: Field>(first: E, second: E){result_type}:
    return first
local def wrapper<E: Field>(value: E, other: E) -> E:
    return pick(value, other)
def mathematical<E: Field>(xs: Vector<E>, initial: E) -> E:
    return fold(elements(xs), initial, fn(state, item) => pick(state, item) + item)
local def local_total<E: Field>(xs: Vector<E>, initial: E) -> E effects(stop):
    result <- ordered(elements(xs), initial, fn(state, item) => pick(state, item) + item)
    return result
pub protocol Demo roles(P)(xs: Vector<F> @P, initial: F @P, other: F @P) -> F @P:
    seed <- wrapper(initial, other)
    first = mathematical(xs, seed)
    second <- local_total(xs, seed)
    return first + second
'''
    package, pin = compile_view(toolchain, journal, directory, source, flags)
    original = joint_package(json.loads(package.read_text()))['original']
    assert '"exec.compute"' in original
    assert run_view(toolchain, journal, directory, package, pin, 'empty',
                    {'xs': [], 'initial': '7', 'other': '99'}) == '14'
    assert run_view(toolchain, journal, directory, package, pin, 'nonempty',
                    {'xs': ['2', '3'], 'initial': '1', 'other': '99'}) == '12'


@pytest.mark.parametrize('flags', FLAGS)
@pytest.mark.parametrize('implementation', ['First', 'Second'])
@pytest.mark.parametrize('caller', ['mathematical', 'local_total',
                                   'mathematical_scoped', 'local_scoped'])
def test_ordinary_view_member_dispatch(toolchain, journal, directory, flags, implementation, caller):
    source = ORDINARY_MEMBERS + '''
pub protocol Demo roles(P)(x: bool @P, y: bool @P, padding: [index; 2] @P) -> bool @P:
'''
    call = f'{caller}<{implementation}<7, index>>(x, y, padding)'
    source += (f'    result <- {call}\n    return result\n'
               if caller.startswith('local') else f'    return {call}\n')
    package, pin = compile_view(toolchain, journal, directory, source, flags)
    original = joint_package(json.loads(package.read_text()))['original']
    if caller.startswith('local'):
        assert '"exec.compute"' in original
    for x, y in itertools.product([False, True], repeat=2):
        expected = x if implementation == 'First' else y
        assert run_view(toolchain, journal, directory, package, pin, f'{x}-{y}',
                        {'x': x, 'y': y, 'padding': ['3', '11']}) is expected


@pytest.mark.parametrize('flags', FLAGS)
@pytest.mark.parametrize('operation', ['and', 'or'])
@pytest.mark.parametrize('left', [False, True])
@pytest.mark.parametrize('operand', ['identity', 'method', 'math_callback', 'first', 'second', 'finite_argument'])
def test_protocol_boolean_view_operands(toolchain, journal, directory, flags, operation, left, operand):
    calls = {'identity': 'identity(x)', 'method': 'box.read()',
             'math_callback': 'apply(x, fn(item) => identity(item))',
             'first': 'M::pick<bool, 2>(x, y, padding)',
             'second': 'M::pick<bool, 2>(x, y, padding)',
             'finite_argument': 'ignore(range(index<0>(), index<2>()), x)'}
    call = calls[operand]
    formula = f'{call} {operation} z' if left else f'z {operation} {call}'
    implementation = 'Second' if operand == 'second' else 'First'
    source = ORDINARY_MEMBERS + f'''
view def identity(value: bool) -> bool:
    return value
view def ignore(rows: Finite<index>, value: bool) -> bool:
    return value
struct Box:
    pub value: bool
pub view def read(self: Box) -> bool:
    return self.value
pub protocol Formula<M: Forward<index>> roles(P)(x: bool @P, y: bool @P, z: bool @P, box: Box @P, padding: [index; 2] @P) -> bool @P:
    return {formula}
pub protocol Demo roles(P)(x: bool @P, y: bool @P, z: bool @P, box: Box @P, padding: [index; 2] @P) -> bool @P:
    result <- Formula<{implementation}<7, index>>(x, y, z, box, padding) @P
    return result
'''
    package, pin = compile_view(toolchain, journal, directory, source, flags)
    for x, y, z in itertools.product([False, True], repeat=3):
        value = y if operand == 'second' else x
        expected = (value and z) if operation == 'and' else (value or z)
        assert run_view(toolchain, journal, directory, package, pin, f'{x}-{y}-{z}',
                        {'x': x, 'y': y, 'z': z, 'box': {'value': x},
                         'padding': ['3', '11']}) is expected
