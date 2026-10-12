"""Source auxiliary columns and claims match the independent staged reference.

The reference constructs its own expression arenas and row-major witnesses;
the source builds columns with generic vector operations. This compares their
values, claim order and scoped residuals for both reductions on all tables.
"""

from source_modules import library_modules
from input_files import input_files
import json
from pathlib import Path

import pytest

from test_machine_relations import machine, reductions
from ring_arena import decode, ZERO

ROOT = Path(__file__).resolve().parents[3]


def test_field_balance_logup_signed_counts_and_inactive_poles(toolchain, journal, directory):
    p = 2130706433
    def base(values):
        return ext_vector([(value % p,) + (0,) * 7 for value in values])
    inputs = {'channels': '1', 'kind': ['0'], 'channel': ['0'], 'side': ['0'],
              'arity': ['1'], 'tuple_degree': ['1'], 'count_degree': ['1'],
              'height': '4', 'values': base([37, 1, 7, 1, 0, 2, p - 1, 3]),
              'challenges': base([37, 5])}
    request = input_files(journal, 'weighted', roles={'P': {'inputs': inputs}})
    arguments = [f'--compiler={toolchain.compiler}',
        f'--module=inspect_reduction={ROOT}/common/tests/protocol/sources/interaction-reduction.zkc',
        *library_modules('air')]
    output = directory / 'weighted-results.json'
    journal.json([toolchain.runtime, '--json', 'run', *arguments,
                  'inspect_reduction::LogUpRun', *request, f'--results={output}'])
    actual = json.loads(output.read_text())['roles']['P']
    inverses = [0, pow(36, -1, p), pow(30, -1, p), pow(36, -1, p)]
    running, total = [], 0
    for count, inverse in zip([0, 2, p - 1, 3], inverses):
        total = (total + count * inverse) % p
        running.append(total)
    assert actual['columns'] == base(inverses + running)
    assert actual['claims'] == base([total])
    assert actual['ranges'] == []
    # Inverse constraints hold everywhere; first/transition/last sum equations
    # apply only on their respective row scopes.
    assert all(actual['residuals'][i] == ['0'] * 8 for i in [0, 1, 2, 3, 4, 9, 10, 11, 15])
    journal.json([toolchain.runtime, '--json', 'run', *arguments,
                  'inspect_reduction::ProductRun', *request], refuses='entry-run-incomplete')


def test_mixed_interactions_range_only_natural_counts(toolchain, journal, directory):
    def base(values):
        return ext_vector([(value,) + (0,) * 7 for value in values])
    inputs = {'channels': '2', 'kind': ['0', '1'], 'channel': ['0', '1'], 'side': ['0', '0'],
        'arity': ['1', '1'], 'tuple_degree': ['1', '1'], 'count_degree': ['1', '1'],
        'height': '2', 'values': base([1, 2, 3, 4, 5, 6, 0, 2]),
        'challenges': base([37, 5, 41, 7])}
    request = input_files(journal, 'mixed', roles={'P': {'inputs': inputs}})
    output = directory / 'mixed-results.json'
    journal.json([toolchain.runtime, '--json', 'run', f'--compiler={toolchain.compiler}',
        f'--module=inspect_reduction={ROOT}/common/tests/protocol/sources/interaction-reduction.zkc',
        *library_modules('air'), 'inspect_reduction::LogUpRun', *request, f'--results={output}'])
    actual = json.loads(output.read_text())['roles']['P']
    # Field weights 3 and 4 are unrestricted. The natural record's count 2
    # violates its Boolean range equation, regardless of the LogUp recurrence.
    assert actual['ranges'] == base([0, 2])


def ext_vector(values):
    return [[str(x) for x in row] for row in values]


def unext(values):
    return [tuple(map(int, row)) for row in values]


def indices(values):
    return [str(v) for v in values]


def record_columns(reduction, t, table, height, data, publics):
    rows = reduction._record_values(t, table, height, data, publics)
    columns = []
    for r in reduction.records[t]:
        width = len(r.tuple_outputs)
        for j in range(width):
            columns.append([rows[i][r][0][j] for i in range(height)])
        columns.append([rows[i][r][1] for i in range(height)])
    return [v for c in columns for v in c]


@pytest.mark.parametrize('kind,entry', [(reductions.LOGUP, 'LogUpRun'),
                                        (reductions.PRODUCT, 'ProductRun')])
def test_source_reduction_matches_independent_staged_reference(toolchain, journal, directory, kind, entry):
    bundle, _ = machine.machine_bundle()
    program = [('add-immediate', 4), ('store', 0), ('load', 1), ('set-immediate', 9),
               ('store', 1), ('load', 0), ('add-immediate', 2), ('halt', 0)]
    rows = machine.layout(machine.execute(program, 1))
    configuration, instance, witness = machine.carriers(bundle, rows)
    publics = [decode(slot[1], v) for slot, v in zip(bundle[1], instance[2])]
    package = directory / 'reduction.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
        f'--module=inspect_reduction={ROOT}/common/tests/protocol/sources/interaction-reduction.zkc',
        *library_modules('air'),
        f'inspect_reduction::{entry}', f'--output={package}'])
    pin = report['package_sha256']
    reduction = reductions.Reduction(kind, bundle, [True, True, True])
    challenges = reductions.fixture_challenges('source-comparison', 4)
    assignment = reduction.assign(configuration, instance, witness, challenges)
    for t, table in enumerate(bundle[3]):
        height, data = reductions.table_data(table, t, configuration, instance, witness)
        values = record_columns(reduction, t, table, height, data, publics)
        interactions = table[8]
        inputs = {
            'channels': 2, 'kind': indices([1] * len(interactions)), 'channel': indices([x[1] for x in interactions]),
            'side': indices([0 if x[4] == 'push' else 1 for x in interactions]),
            'arity': indices([len(x[5]) for x in interactions]),
            'tuple_degree': indices([2] * len(interactions)),
            'count_degree': indices([1] * len(interactions)),
            'values': ext_vector(values), 'height': height,
            'challenges': ext_vector(challenges)}
        request = input_files(journal, f'{entry}-{t}.json', session=f'{entry}{t}', roles={'P': {'inputs': inputs}})
        result = directory / f'{entry}-{t}.out.json'
        journal.json([toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', *request, f'--results={result}'])
        actual = json.loads(result.read_text())['roles']['P']
        columns = unext(actual['columns'])
        width = len(reduction.columns[t])
        expected = [decode(reduction.field, v) for v in assignment[2][0][2][t][0]]
        # reference is row-major height x width, source is column-major
        transposed = [expected[i * width + c] for c in range(width) for i in range(height)]
        assert columns == transposed, (kind, t)
        claims = unext(actual['claims'])
        ref_claims = [decode(reduction.field, assignment[2][0][1][reduction.claim_index[(t, key)]])
                      for role, key in reduction.columns[t] if role != 'inverse']
        assert claims == ref_claims, (kind, t, claims, ref_claims)
        residuals = unext(actual['residuals'])
        layout_count = len(reduction.assertion_names[t])
        assert len(residuals) == layout_count * height, (len(residuals), layout_count)
        # Every residual on its scope is zero.
        for k, name in enumerate(reduction.assertion_names[t]):
            block = residuals[k * height:(k + 1) * height]
            scope = reduction.program[2][0][2][t][3][k][1]
            active = {'all': range(height), 'first': [0], 'last': [height - 1]}.get(scope[0])
            if scope[0] == 'interior':
                active = range(scope[1], height - scope[2])
            assert all(block[i] == ZERO for i in active), (kind, t, name)
        ranges = unext(actual['ranges'])
        assert all(v == ZERO for v in ranges)
