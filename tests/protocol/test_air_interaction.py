"""Source auxiliary columns and claims match the independent staged reference.

The reference constructs its own expression arenas and row-major witnesses;
the source builds columns with generic vector operations. This compares their
values, claim order and scoped residuals for both reductions on all tables.
"""
import json
from pathlib import Path

import pytest

from test_machine_relations import machine, reductions
from ring_arena import decode, ZERO

ROOT = Path(__file__).resolve().parents[2]


def ext_vector(values):
    return (b'ZKCV\x00\x1b' + len(values).to_bytes(4, 'little')
            + b''.join(x.to_bytes(4, 'little') for v in values for x in v)).hex()


def unext(hexed):
    raw = bytes.fromhex(hexed)
    assert raw[:6] == b'ZKCV\x00\x1b'
    n = int.from_bytes(raw[6:10], 'little')
    xs = [int.from_bytes(raw[10 + 4 * i:14 + 4 * i], 'little') for i in range(8 * n)]
    return [tuple(xs[8 * i:8 * i + 8]) for i in range(n)]


def indices(values):
    return (b'ZKCV\x00\x44' + len(values).to_bytes(4, 'little')
            + b''.join(v.to_bytes(8, 'little') for v in values)).hex()


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
    package = directory / 'reduction.entry'
    report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
        f'--module=inspect_reduction={ROOT}/tests/protocol/sources/interaction-reduction.zkc',
        f'--module=air_polynomial={ROOT}/libraries/air/polynomial.zkc',
        f'--module=air_interaction={ROOT}/libraries/air/interaction.zkc',
        f'--entry=inspect_reduction::{entry}', f'--output={package}'])
    pin = report['package_sha256']
    reduction = reductions.Reduction(kind, bundle, [True, True, True])
    challenges = reductions.fixture_challenges('source-comparison', 4)
    assignment = reduction.assign(configuration, instance, witness, challenges)
    for t, table in enumerate(bundle[3]):
        height, data = reductions.table_data(table, t, configuration, instance, witness)
        values = record_columns(reduction, t, table, height, data, publics)
        interactions = table[8]
        inputs = {
            'channels': 2, 'channel': indices([x[1] for x in interactions]),
            'side': indices([0 if x[4] == 'push' else 1 for x in interactions]),
            'arity': indices([len(x[5]) for x in interactions]),
            'tuple_degree': indices([2] * len(interactions)),
            'count_degree': indices([1] * len(interactions)),
            'values': ext_vector(values), 'height': height,
            'challenges': ext_vector(challenges)}
        request = journal.write(f'{entry}-{t}.json', {
            'format': 'zkc.entry-run/0', 'session': f'{entry}{t}',
            'roles': {'P': {'inputs': inputs}}})
        result = directory / f'{entry}-{t}.out.json'
        journal.json([toolchain.runtime, 'run', package, pin, request, f'--results={result}'])
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
