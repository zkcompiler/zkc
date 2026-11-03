"""Hand-authored native selected Math through actual Program export and CPU Host."""
import hashlib
import itertools
import json
from pathlib import Path

import pytest

FIXTURES = Path(__file__).resolve().parents[3] / 'compiler/test/fixtures/control'


def wire(tag, payload):
    return b'ZKCV\x00' + bytes([tag]) + payload


def boolean(value):
    return wire(5, bytes([value]))


def index(value):
    return wire(31, value.to_bytes(8, 'little'))


def field(value):
    return wire(1, value.to_bytes(32, 'little'))


def variant(alternative, *payload):
    return wire(65, alternative.to_bytes(4, 'little') + b''.join(
        len(child).to_bytes(4, 'little') + child for child in payload))


def compile_bundle(toolchain, journal, directory, name, flags):
    bundle = directory / f'{name}.bundle'
    text = journal.run([toolchain.compiler, 'protocol-bundle',
                        FIXTURES / f'{name}.mlir', *flags], keep=f'{name}-bundle.json')
    bundle.write_text(text)
    program = json.loads(json.loads(text)['candidate'])
    assert program[0] == 'zkc.program/0'
    # Inspect the actual emitted Program rather than substituting an evaluator.
    assert '"if"' in json.dumps(program) or '"match"' in json.dumps(program)
    return bundle, program[3][0][4]


def execute(toolchain, journal, directory, compiled, name, values, capacity=None):
    bundle, ports = compiled
    inputs = directory / f'{name}-inputs.json'
    inputs.write_text(json.dumps(['zkc.bundle-inputs/0', 'selected-math', [['P', [
        [str(i), port[1], ['wire', value.hex()]]
        for i, (port, value) in enumerate(zip(ports, values))
    ], []]], []]))
    command = [toolchain.runtime, '--json', 'bundle', 'run', bundle,
               hashlib.sha256(bundle.read_bytes()).hexdigest(), inputs, '--threads=1']
    if capacity is not None:
        path = directory / f'{name}-capacity.json'
        path.write_text(json.dumps(capacity))
        command.append(f'--capacity={path}')
    result = journal.attempt(command, keep=f'{name}-result.json')
    assert result.returncode in (0, 1), result.stderr
    report = json.loads(result.stdout)
    assert report['format'] == 'zkc.bundle-result/0'
    assert report.get('roles'), report
    assert all(role['active_frames'] == role['live_resource_units'] == 0
               for role in report['roles']), report
    return report


def completed(report, expected):
    assert report['outcome'] == ['completed'], report
    assert [value[2] for value in report['roles'][0]['outputs']] == [v.hex() for v in expected]


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_boolean_nested_helpers_and_tuple(toolchain, journal, directory, flags):
    simple = compile_bundle(toolchain, journal, directory, 'math', flags)
    for choice in (False, True):
        completed(execute(toolchain, journal, directory, simple, f'bool-{choice}',
                          [boolean(choice), index(11), index(23)]),
                  [index(11 if choice else 23)])
    aliased = compile_bundle(toolchain, journal, directory, 'math-alias', flags)
    for choice in (False, True):
        completed(execute(toolchain, journal, directory, aliased, f'alias-{choice}',
                          [boolean(choice), index(11), index(23)]), [index(11)])
    nested = compile_bundle(toolchain, journal, directory, 'math-nested', flags)
    for outer, inner in itertools.product((False, True), repeat=2):
        left = 10 if inner else 7
        first, second = (left, left) if outer else (7, 3)
        completed(execute(toolchain, journal, directory, nested, f'nested-{outer}-{inner}',
                          [boolean(outer), boolean(inner), field(3), field(7)]),
                  [variant(0, field(first), field(second)), field(first), field(second)])


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_all_enum_arms_exact_payloads_and_record_fields(toolchain, journal, directory, flags):
    compiled = compile_bundle(toolchain, journal, directory, 'math-match', flags)
    for arm, payload, count, value in [
            (0, [], 11, 3), (1, [field(7)], 11, 14),
            (2, [index(23), field(17)], 23, 17), (3, [], 0, 3)]:
        completed(execute(toolchain, journal, directory, compiled, f'arm-{arm}',
                          [variant(arm, *payload), index(11), field(3)]),
                  [variant(0, index(count), field(value)), index(count), field(value)])


@pytest.mark.parametrize('flags', [[], ['--no-finite-bulk'],
                                   ['--fuse-collect-fold', '--fuse-vector-reductions']])
def test_selected_math_inside_and_around_finite_work(toolchain, journal, directory, flags):
    compiled = compile_bundle(toolchain, journal, directory, 'math-finite', flags)
    for enabled, count in itertools.product((False, True), (0, 1, 3)):
        completed(execute(toolchain, journal, directory, compiled, f'finite-{enabled}-{count}',
                          [boolean(enabled), index(count), field(5)]),
                  [index(count if enabled else 0), field(5 * (count + 1) if enabled else 5)])


@pytest.mark.parametrize('flags', [[], ['--no-finite-bulk']])
def test_expensive_valid_dormant_arm_performs_no_work_or_allocation(toolchain, journal, directory, flags):
    compiled = compile_bundle(toolchain, journal, directory, 'math-allocation', flags)
    small = execute(toolchain, journal, directory, compiled, 'small-dormant',
                    [boolean(False), index(1), field(5)])
    large = execute(toolchain, journal, directory, compiled, 'large-dormant',
                    [boolean(False), index(20000), field(5)])
    completed(small, [index(0)])
    completed(large, [index(0)])
    assert small['roles'][0]['usage'] == large['roles'][0]['usage']
    assert large['roles'][0]['usage']['iterations'] == 0
    entered = execute(toolchain, journal, directory, compiled, 'entered',
                      [boolean(True), index(8), field(5)])
    completed(entered, [index(8)])
    assert entered['roles'][0]['usage']['total_value_bytes'] > large['roles'][0]['usage']['total_value_bytes']
    capacity = large['limits']['capacity']
    capacity[5][1] = '0'
    skipped = execute(toolchain, journal, directory, compiled, 'zero-iteration-dormant',
                      [boolean(False), index(20000), field(5)], capacity)
    completed(skipped, [index(0)])
    refused = execute(toolchain, journal, directory, compiled, 'zero-iteration-entered',
                      [boolean(True), index(8), field(5)], capacity)
    assert refused['outcome'] != ['completed']
    assert refused['roles'][0]['after'][1]['cause'] == ['limit']
    assert refused['roles'][0]['usage']['iterations'] == 0


@pytest.mark.parametrize('flags', [[], ['--no-calculation-batching']])
def test_selected_value_survives_multiple_demand_cuts(toolchain, journal, directory, flags):
    compiled = compile_bundle(toolchain, journal, directory, 'math-demand', flags)
    for choice in (False, True):
        expected = 10 if choice else 7
        completed(execute(toolchain, journal, directory, compiled, f'demand-{choice}',
                          [boolean(choice), field(3), field(7), field(expected)]),
                  [field(expected), field(2 * expected)])
