"""Exact table predicates, retained subjects and a distinct AIR verifier control."""
import json
from pathlib import Path

import pytest

from entry import joint_package
from input_files import input_files

PROJECT = Path(__file__).resolve().parents[3] / 'examples/projects/table/zkc.toml'


def compile_table(toolchain, journal, directory, entry):
    package = directory / f'{entry}.zkpkg'
    result = journal.json([toolchain.runtime, '--json', 'compile',
                           f'--compiler={toolchain.compiler}', f'--project={PROJECT}',
                           f'example::{entry}', f'--output={package}'])
    return package, result['package_sha256']


def run_table(toolchain, journal, directory, package, pin, name, arguments, refuses=None):
    request = input_files(journal, name, package=package, arguments=arguments)
    output = directory / f'{name}.results.json'
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={pin}', *request, f'--results={output}'], refuses=refuses)
    if refuses:
        assert report['status'] == 'refused'
        assert not output.exists(), 'a terminal stop published a returned value'
        return report
    assert report['status'] == 'executed'
    return json.loads(output.read_text())['value']


@pytest.mark.parametrize('entry', ['Membership', 'Direct'])
def test_exact_membership_and_selection(toolchain, journal, directory, entry):
    package, pin = compile_table(toolchain, journal, directory, entry)
    if entry == 'Membership':
        child = joint_package(json.loads(package.read_text()))
        interface = json.loads(child['interface'])
        assert len(interface['relations']) == 1
        definition = interface['relations'][0]['definition']
        assert definition['kind'] == 'formula'
        assert definition['function'] in child['original']
        assert 'zkc.language.formula/0' in child['original']
        clauses = [c for p in interface['protocols'] for c in p['clauses']]
        assert len(clauses) == 1
        # The exact selector mapping, masks and values remain in the original;
        # native reader mutation controls separately establish their authority.
        assert 'selected_rows' in json.dumps(clauses)
    cases = [
        ('empty', [], [], [], True),
        ('absent', [], [1], [True], False),
        ('inactive', [], [1], [False], True),
        ('found', [1], [1], [True], True),
        ('wrong-table', [2], [1], [True], False),
        ('duplicate-queries', [1], [1, 1], [True, True], True),
        ('duplicate-table', [1, 1], [1], [True], True),
        ('masked', [1], [2, 1], [False, True], True),
        ('mask-changed', [1], [2, 1], [True, True], False),
    ]
    for name, table, values, active, expected in cases:
        result = run_table(toolchain, journal, directory, package, pin, name,
                           {'table': table, 'values': values, 'active': active})
        assert (result if entry == 'Direct' else result['V']['accepted']) is expected


def test_indexed_reads_keep_coordinate_identity(toolchain, journal, directory):
    package, pin = compile_table(toolchain, journal, directory, 'IndexedRead')
    cases = [('empty', [], 0, 1, False), ('first', [1, 2], 0, 1, True),
             ('second', [1, 2], 1, 2, True), ('wrong-position', [1, 2], 0, 2, False),
             ('wrong-value', [1, 2], 1, 1, False), ('past-end', [1, 2], 2, 1, False),
             ('max-index', [1, 2], 2**64 - 1, 1, False)]
    for name, table, position, value, expected in cases:
        result = run_table(toolchain, journal, directory, package, pin, name,
                           {'table': table, 'position': position, 'value': value})
        assert result['V']['accepted'] is expected


def test_reached_mask_descriptor_is_checked_before_empty_traversal(toolchain, journal, directory):
    package, pin = compile_table(toolchain, journal, directory, 'Direct')
    report = run_table(toolchain, journal, directory, package, pin, 'malformed',
                       {'table': [], 'values': [], 'active': [True]},
                       refuses='entry-host-numeric-stopped')
    assert not report['execution']['completed']


def test_air_reciprocal_control_is_not_membership(toolchain, journal, directory):
    package, pin = compile_table(toolchain, journal, directory, 'InteractionControl')
    modulus = 2130706433
    gamma = 4 * pow(3, -1, modulus) % modulus
    table, values = [1, 2], [0, 0]
    reciprocals = [pow((gamma - value) % modulus, -1, modulus)
                   for value in values + table]
    result = run_table(toolchain, journal, directory, package, pin, 'false-membership',
                       {'table': table, 'values': values, 'active': [True, True],
                        'gamma': gamma, 'reciprocals': reciprocals})
    assert result['V'] == {'membership': False, 'interaction': True}
    reciprocals[0] = (reciprocals[0] + 1) % modulus
    result = run_table(toolchain, journal, directory, package, pin, 'wrong-reciprocal',
                       {'table': table, 'values': values, 'active': [True, True],
                        'gamma': gamma, 'reciprocals': reciprocals})
    assert result['V'] == {'membership': False, 'interaction': False}
