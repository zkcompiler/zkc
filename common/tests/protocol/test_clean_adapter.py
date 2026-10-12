"""Clean extraction, native Bundle semantics and ordinary source proofs."""

from copy import deepcopy
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[3]
ADAPTER = ROOT / 'compiler/adapters/clean'
sys.path.insert(0, str(ADAPTER.parent))
sys.path.insert(0, str(ADAPTER))
from adapter import Table, check_cardinality, export  # noqa: E402
from ring_arena import P, Refusal, compact, identity  # noqa: E402


def fixture(name):
    path = ADAPTER / 'fixtures' / name
    return [json.loads((path / f'{part}.json').read_text())
            for part in ('bundle', 'configuration', 'instance', 'witness')]


def evaluate(toolchain, journal, candidates):
    wire = ''.join(compact(candidate) + '\n' for candidate in candidates)
    results = []
    for executable in (toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')):
        results.append([json.loads(line) for line in journal.run([executable], stdin=wire).splitlines()])
    assert results[0] == results[1]
    assert all(result['accepted'] for result in results[0])
    return [result['result']['satisfied'] for result in results[0]]


@pytest.mark.parametrize('name', ['fibonacci', 'femtocairo', 'flat-channel', 'table-scopes'])
def test_clean_extraction_regenerates_native_carriers(name):
    path = ADAPTER / 'fixtures' / name
    source = json.loads((path / 'source.json').read_text())
    for filename, value in export(source).documents().items():
        assert compact(value) + '\n' == (path / filename).read_text()
    # FemtoCairo uses Clean's Spec interpreter; Fibonacci uses a local recursive
    # reference. Neither evaluates the exported constraints to obtain the answer.
    if reference := source.get('reference'):
        assert source['trace'][-1][:len(reference)] == reference
        assert source['public'][-len(reference):] == reference


def test_fibonacci_frontends_match_independent_recurrence(toolchain, journal):
    clean = fixture('fibonacci')
    path = ROOT / 'compiler/adapters/plonky3/fixtures/fibonacci'
    plonky = [json.loads((path / f'{name}.json').read_text()) for name in
              ('bundle', 'bundle-configuration', 'bundle-instance', 'bundle-witness')]
    x, y, trace = 0, 1, []
    for _ in range(8):
        trace.extend([str(x), str(y)])
        x, y = y, (x + y) % P
    assert clean[3][2][0][0] == plonky[3][2][0][0] == trace
    assert evaluate(toolchain, journal, [clean, plonky]) == [True, True]
    cases = []
    for candidate in (clean, plonky):
        for position in (0, 1, 4, 9, 14, 15):
            changed = deepcopy(candidate)
            changed[3][2][0][0][position] = str(int(trace[position]) + 1)
            cases.append(changed)
    assert evaluate(toolchain, journal, cases) == [False] * len(cases)


def test_vm_memory_program_counts_and_public_boundaries(toolchain, journal):
    honest = fixture('femtocairo')
    assert max(map(int, honest[3][2][2][0][2::3])) > 1  # Repeated memory reads.
    assert evaluate(toolchain, journal, [honest]) == [True]
    cases = []
    # CPU transition, program value, indexed address, selector, memory value,
    # program multiplicity, memory multiplicity and public final PC.
    paths = [(3, 2, 0, 0, 34), (1, 2, 1, 1, 0, 1), (3, 2, 2, 0, 3),
             (3, 2, 0, 0, 33), (3, 2, 2, 0, 4), (3, 2, 1, 0, 0),
             (3, 2, 2, 0, 2), (2, 2, 3)]
    for path in paths:
        changed = deepcopy(honest)
        cursor = changed
        for index in path[:-1]:
            cursor = cursor[index]
        cursor[path[-1]] = str((int(cursor[path[-1]]) + 1) % P)
        cases.append(changed)
    assert evaluate(toolchain, journal, cases) == [False] * len(cases)
    # Auxiliary columns of the initial row are outside the source's finite
    # transition windows. Wrapping inactive lookups must not constrain them.
    inactive = deepcopy(honest)
    inactive[3][2][0][0][3] = '123'
    assert evaluate(toolchain, journal, [inactive]) == [True]


def test_clean_flat_component_retains_signed_channel_balance(toolchain, journal):
    source = json.loads((ADAPTER / 'fixtures/flat-channel/source.json').read_text())
    assert any('interact' in op and 'assume_guarantees' in op['interact']
               for op in source['table']['operations'])
    native = fixture('flat-channel')
    assert export(source).bundle == native[0]
    changed = deepcopy(native)
    changed[3][2][0][0][256 + 42] = str(P - 2)
    assert evaluate(toolchain, journal, [native, changed]) == [True, False]


def test_vm_pins_reject_attacks_that_preserve_lookup_balance(toolchain, journal):
    source = json.loads((ADAPTER / 'fixtures/femtocairo/source.json').read_text())
    address, program, selector = [fixture('femtocairo') for _ in range(3)]
    # Unqueried cells contribute zero to the balance, but are still constrained.
    assert address[3][2][2][0][23] == '0'
    address[3][2][2][0][21] = '1'
    assert program[3][2][1][0][28] == '0'
    program[1][2][1][1][0][57] = '5'
    # Skip row zero and compensate every lookup multiplicity. Evaluate source
    # expressions independently of the adapter and its generated ring arena.
    ctx = source['table']['operations'][0]['context']

    def value(expr):
        match expr['type']:
            case 'const':
                return expr['value']
            case 'var':
                cell = ctx['vars'][expr['index']]
                return source['trace'][cell['row']][cell['column']]
            case 'add':
                return (value(expr['lhs']) + value(expr['rhs'])) % P
            case 'mul':
                return (value(expr['lhs']) * value(expr['rhs'])) % P
            case _:
                raise AssertionError(expr)

    selector[3][2][0][0][33] = '0'
    removed = {'program': 0, 'memory': 0}
    for op in ctx['circuit']:
        if 'lookup' not in op:
            continue
        lookup = op['lookup']
        index, _ = map(value, lookup['entry'])
        table, position = (1, index) if lookup['table'] == 'program' else (2, index * 3 + 2)
        counts = selector[3][2][table][0]
        assert int(counts[position]) > 0
        counts[position] = str(int(counts[position]) - 1)
        removed[lookup['table']] += 1
    assert removed == {'program': 4, 'memory': 6}
    cases = [address, program, selector]
    assert evaluate(toolchain, journal, cases) == [False] * 3
    # Disable only the relevant pin by giving it an empty scope. The same bad
    # witnesses must then satisfy every remaining assertion and channel balance.
    for candidate, table, scope in zip(cases, [2, 1, 0],
                                       [['interior', 0, 1], ['interval', 25, 32], ['interval', 0, 7]]):
        pins = [a for a in candidate[0][3][table][7] if a[1] == scope]
        assert len(pins) == 1
        pins[0][1] = ['interval', 0, 0]
        for carrier in candidate[1:]:
            carrier[1] = identity(candidate[0])
    assert evaluate(toolchain, journal, cases) == [True] * 3


def test_channel_cardinality_counts_zero_weight_records():
    table = Table('zero_weights', 1 << 20, [], records=[(0, [], 0)] * (P >> 20))
    assert table.height * len(table.records) == P - 1
    check_cardinality([table], [['bytes']])
    table.records.append((0, [], 0))
    with pytest.raises(Refusal, match='clean-channel-characteristic'):
        check_cardinality([table], [['bytes']])


def test_all_row_lookup_needs_no_selector(toolchain, journal):
    source = {'format': 'zkc.clean-export/0', 'field': P,
        'table': {'model': 'table', 'height': 2, 'width': 1, 'operations': [{
            'type': 'EveryRow', 'context': {'window': 1, 'vars': [{'row': 0, 'column': 0}],
                'circuit': [{'lookup': {'table': 'values', 'entry': [
                    {'type': 'const', 'value': 0}, {'type': 'var', 'index': 0}]}}]}}]},
        'public_bindings': [], 'public': [], 'lookups': [
            {'name': 'values', 'interpretation': 'fixed-indexed', 'values': [7]}],
        'trace': [[7], [7]], 'witness_tables': {}}
    native = list(export(source).documents().values())
    assert native[0][3][0][4][0][3] == 1
    assert evaluate(toolchain, journal, [native]) == [True]
    native[3][2][0][0][0] = '8'
    assert evaluate(toolchain, journal, [native]) == [False]


def test_one_row_auxiliaries_have_independent_columns(toolchain, journal):
    native = fixture('table-scopes')
    assert evaluate(toolchain, journal, [native]) == [True]
    cases = []
    for position in (2, 6, 7):
        changed = deepcopy(native)
        changed[3][2][0][0][position] = '99'
        cases.append(changed)
    assert evaluate(toolchain, journal, cases) == [False] * 3
    inactive = deepcopy(native)
    inactive[3][2][0][0][3] = '99'
    assert evaluate(toolchain, journal, [inactive]) == [True]


def test_examples_regenerate_inputs(journal):
    for project in ('fibonacci', 'femtocairo'):
        journal.run([sys.executable, ROOT / 'examples/projects' / project / 'prepare.py', '--check'])


@pytest.mark.parametrize('change,code', [
    ('unregistered', 'clean-lookup-unregistered'),
    ('interpretation', 'clean-lookup-interpretation'),
    ('variable', 'clean-variable'),
    ('noncanonical', 'clean-shape'),
    ('extra', 'clean-schema'),
    ('raw-interaction', 'clean-interaction'),
    ('table-channels', 'clean-interaction'),
    ('missing-lookup-name', 'clean-schema'),
    ('missing-witness-table', 'clean-lookup-shape'),
    ('extra-witness-table', 'clean-schema'),
    ('window', 'clean-window'),
    ('witness-lookup', 'clean-witness-lookup'),
    ('duplicate', 'clean-lookup-duplicate'),
])
def test_clean_refuses_unrepresented_source_semantics(change, code):
    source = json.loads((ADAPTER / 'fixtures/femtocairo/source.json').read_text())
    if change == 'unregistered':
        source['lookups'] = source['lookups'][1:]
    elif change == 'interpretation':
        source['lookups'][1]['interpretation'] = 'arbitrary-Lean-proposition'
    elif change == 'variable':
        source['table']['operations'][0]['context']['circuit'].append(
            {'assert': {'type': 'var', 'index': 1000}})
    elif change == 'noncanonical':
        source['trace'][0][0] = P
    elif change == 'extra':
        source['verifier'] = {}  # Must never silently omit an ensemble verifier.
    elif change == 'raw-interaction':
        source['table']['operations'][0]['context']['circuit'].append({'interact': {}})
    elif change == 'table-channels':
        source['channels'] = [{'name': 'unused', 'arity': 1}]
    elif change == 'missing-lookup-name':
        del source['lookups'][0]['name']
    elif change == 'missing-witness-table':
        source['witness_tables'] = {}
    elif change == 'extra-witness-table':
        source['witness_tables']['extra'] = []
    elif change == 'window':
        source['table']['operations'][0]['context']['window'] = 1
    elif change == 'witness-lookup':
        source['witness_tables']['memory'][1] = 99
    elif change == 'duplicate':
        source['lookups'].append(source['lookups'][0])
    with pytest.raises(Refusal) as failure:
        export(source)
    assert failure.value.code == code


@pytest.mark.parametrize('change,code', [('row', 'clean-boundary'),
    ('missing-row', 'clean-schema'), ('window', 'clean-window')])
def test_boundary_schema_matches_one_row_clean_operations(change, code):
    source = json.loads((ADAPTER / 'fixtures/table-scopes/source.json').read_text())
    operation = source['table']['operations'][1]
    if change == 'row':
        operation['row'] = 2
    elif change == 'missing-row':
        del operation['row']
    else:
        operation['row'] = 0
        operation['context']['window'] = 2
    with pytest.raises(Refusal) as failure:
        export(source)
    assert failure.value.code == code


@pytest.mark.parametrize('change,code', [('unregistered', 'clean-channel-unregistered'),
    ('arity', 'clean-channel-arity'), ('width', 'clean-shape')])
def test_component_refuses_unrepresented_channel_shape(change, code):
    source = json.loads((ADAPTER / 'fixtures/flat-channel/source.json').read_text())
    if change == 'unregistered':
        source['channels'] = []
    elif change == 'arity':
        source['channels'][0]['arity'] = 2
    else:
        source['table']['width'] = '256'
    with pytest.raises(Refusal) as failure:
        export(source)
    assert failure.value.code == code


@pytest.mark.parametrize('project,entry', [('fibonacci', 'CleanProof'),
    ('fibonacci', 'Plonky3Proof'), ('femtocairo', 'Proof')])
def test_external_relations_use_ordinary_source_proofs(toolchain, journal, directory, project, entry):
    base = ROOT / 'examples/projects' / project
    arguments = [f'--compiler={toolchain.compiler}', f'--project={base}/zkc.toml', f'example::{entry}']
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *arguments, f'--output={proof}'])
    assert produced['status'] == 'produced'
    checked = journal.json([toolchain.runtime, '--json', 'verify', *arguments, f'--proof={proof}'])
    assert checked['status'] == 'accepted'
    public = json.loads((base / f'inputs/example.{entry}/public.json').read_text())
    if project == 'fibonacci':
        public['final_x'] = '14'
    else:
        public['statement']['public_data'][3] = '29'
    path = journal.write('changed-public.json', public)
    rejected = journal.attempt([toolchain.runtime, '--json', 'verify', *arguments,
                               f'--public={path}', f'--proof={proof}'])
    assert rejected.returncode > 0
    report = json.loads(rejected.stdout)
    assert report['code'] == 'proof-header'
    # The honest prover also refuses the false statement's quotient. This is
    # a completeness control, separate from malicious-prover verifier tests.
    false_proof = directory / 'false-proof.bin'
    stopped = journal.json([toolchain.runtime, '--json', 'prove', *arguments,
                  f'--public={path}', f'--output={false_proof}'], refuses='artifact-stopped')
    assert stopped['execution']['stop']['kind'] == 'Explicit("reject")'
    assert not false_proof.exists()
