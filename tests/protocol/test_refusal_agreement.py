"""Phase-scoped refusals; three independent readers, shared expectations only.

Rust reads physical participants, not common sources. Native negative cases
must fail before the correspondence checker; a forwarded Lean refusal cannot
count as Rust agreement. Locations and useful trailing detail may differ.
"""
import copy
import json
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / 'tests/fixtures/refusal-agreement'
SOURCE = json.loads((FIXTURES / 'source.json').read_text())
CASES = json.loads((FIXTURES / 'cases.json').read_text())


def function(carrier, name):
    functions = carrier[3] if carrier[0] == 'zkc.participants/1' else carrier[2]
    return next(f for f in functions if f[5] == [name, []])


def mutate(carrier, row):
    """Apply the same semantic defect to source and participant spellings."""
    physical = carrier[0] == 'zkc.participants/1'
    name = row['name']
    if name == 'reuse':
        f = function(carrier, 'Use')
        f[4][1][4] = [f[2][0][0]]
    elif name == 'duplicate-result':
        f = function(carrier, 'Make')
        f[3] *= 2
        f[4][-1][1] *= 2
    elif name in ('domain', 'slot', 'slot-arity', 'implementation'):
        binding = next(b for b in carrier[1] if b[0] == ('pass' if name == 'domain' else 'create'))
        if name == 'implementation': binding[3] = 'arkworks/resource_unit.create'
        else: binding[2] = [] if name == 'slot-arity' else ['Slot.B' if name == 'domain' else '0invalid']
    elif name == 'attributes':
        function(carrier, 'Make')[4][0][3] = ['payload']
    elif 'attributes' in row:
        function(carrier, row['function'])[4][0][3] = row['attributes']
    elif 'place' in row:
        place, value = row['place'], row['value']
        if place == 'loop':
            body = carrier[4][0][7] if physical else carrier[3][0][7]
            body[0][2] = value if physical else ['constant', value]
        elif place == 'parameter':
            carrier[4][0][4 if physical else 3][0][1] = value
        elif place == 'curve-index':
            function(carrier, 'At')[4][0][3] = [value]
        else:
            function(carrier, 'Count' if place == 'index' else 'Scalar')[4][0][3] = [value]
    elif name == 'region-terminal':
        function(carrier, 'Choose')[4][0][4][0][0] = 'return'
    elif name == 'branch-yield':
        f = function(carrier, 'Choose')
        f[4][0][5][0][1] = [f[2][0][0]]
    elif name == 'loop-yield':
        function(carrier, 'Fold')[4][0][7][0][1] = []
    elif name == 'match-yield':
        f = function(carrier, 'Match')
        f[4][0][4][1][2][0][1] = [f[2][1][0]]
    elif name == 'if-stopped-outputs':
        branch = function(carrier, 'Choose')[4][0]
        branch[4] = [['stop', 'left', *([] if physical else ['']), 'reject']]
        branch[5] = [['stop', 'right', *([] if physical else ['']), 'reject']]
    elif name == 'match-stopped-outputs':
        arms = function(carrier, 'Match')[4][0][4]
        for label, _, body in arms:
            body[:] = [['stop', label, *([] if physical else ['']), 'reject']]
    elif name == 'function-return':
        function(carrier, 'Choose')[4][-1][1] = []
    elif name.startswith('variant-'):
        spelling = 'variant:' + json.dumps(row['graph'], separators=(',', ':')).encode().hex()
        function(carrier, 'Inspect')[2][0][1] = spelling + ('@logical.variant/1' if physical else '')
    else:
        raise AssertionError(f'unknown mutation: {name}')


def leading(reason):
    return reason.split(':', 1)[0]


def compiler_refusal(journal, command, reason):
    result = journal.attempt(command)
    assert result.returncode > 0, result.stdout
    # Read the leading diagnostic, never a filename or a trailing detail.
    found = re.search(
        r'^(?:[^\n]+:\d+:\d+:\s*(?:error:\s*)?|error:\s*)'
        r'([a-z][a-z0-9-]+)(?=[:\s]|$)', result.stderr, re.MULTILINE)
    assert found and found[1] == reason, result.stderr


def lean_refusal(journal, command, reason):
    result = journal.attempt(command)
    assert result.returncode > 0, result.stdout
    response = json.loads(result.stdout)
    assert response[0] == 'refused', response
    assert leading(response[1]) == reason, response


def native_run(journal, toolchain, source, candidate):
    inputs = journal.write('inputs.json', ['zkc.run/2', 'main', 'session', [], [['P', [], [], []]], []])
    return journal.attempt([toolchain.runtime, 'run-protocol', source, candidate, inputs,
                            toolchain.checker('interactive-protocol')])


@pytest.mark.parametrize('row', CASES, ids=[r['name'] for r in CASES])
@pytest.mark.parametrize('carrier', ['source', 'physical'])
def test_shared_admission_reason(toolchain, journal, row, carrier):
    source = journal.write('source.json', SOURCE)
    if carrier == 'source':
        changed = copy.deepcopy(SOURCE)
        mutate(changed, row)
        path = journal.write('mutated.json', changed)
        compiler_refusal(journal, [toolchain.compiler, 'protocol-admit', path], row['reason'])
        lean_refusal(journal, [toolchain.checker('interactive-protocol'), '--admit', path], row['reason'])
        return

    candidate = json.loads(journal.run([toolchain.compiler, 'protocol-compile', source]))
    mutate(candidate, row)
    path = journal.write('mutated.json', candidate)
    compiler_refusal(journal, [toolchain.compiler, 'protocol-import', path], row['reason'])
    lean_refusal(journal, [toolchain.checker('interactive-protocol'), '--check', source, path], row['reason'])
    result = native_run(journal, toolchain, source, path)
    assert result.returncode > 0, result.stdout
    response = json.loads(result.stdout)
    assert response['status'] == 'refused', response
    category, reason = response['code'].split(': ', 1)
    assert category == row['native_category'], (row['phase'], response)
    assert leading(reason) == row['reason'], (row['phase'], response)
    if 'native_detail' in row:
        assert reason == row['reason'] + ': ' + row['native_detail'], response


@pytest.mark.parametrize('domain', ['Slot.A', 'Slot.B'])
@pytest.mark.parametrize('curve_index', ['0', '1048576'])
def test_positive_control(toolchain, journal, domain, curve_index):
    # Both nominal slots are valid when declarations and uses agree exactly.
    source_value = json.loads(json.dumps(SOURCE).replace('Slot.A', domain))
    function(source_value, 'At')[4][0][3] = [curve_index]
    # Vector sizes share the curve index bound.
    function(source_value, 'Splat')[4][0][3] = [curve_index]
    source = journal.write('source.json', source_value)
    journal.run([toolchain.compiler, 'protocol-admit', source])
    journal.run([toolchain.checker('interactive-protocol'), '--admit', source])
    candidate = journal.write('candidate.json', json.loads(journal.run([
        toolchain.compiler, 'protocol-compile', source])))
    journal.run([toolchain.compiler, 'protocol-import', candidate])
    journal.run([toolchain.checker('interactive-protocol'), '--check', source, candidate])
    result = native_run(journal, toolchain, source, candidate)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert json.loads(result.stdout)['outcome'] == ['returned', {'P': []}]


@pytest.mark.parametrize('stage', ['logical', 'physical'])
def test_well_formed_plan_mismatch_is_a_separate_phase(toolchain, journal, stage):
    source = journal.write('source.json', SOURCE)
    command = 'protocol-compile' if stage == 'physical' else 'protocol-project'
    candidate = json.loads(journal.run([toolchain.compiler, command, source]))
    function(candidate, 'Count')[4][0][3] = ['2']
    path = journal.write('changed-plan.json', candidate)
    journal.run([toolchain.compiler, 'protocol-import', path])
    lean_refusal(journal, [toolchain.checker('interactive-protocol'), '--check', source, path],
                 'source-local-unmatched')
    if stage == 'physical':
        result = native_run(journal, toolchain, source, path)
        assert result.returncode > 0, result.stdout
        response = json.loads(result.stdout)
        assert response['status'] == 'refused', response
        assert response['code'].startswith('Correspondence:'), response
        assert response['code'].endswith('checker-refused:source-local-unmatched'), response
