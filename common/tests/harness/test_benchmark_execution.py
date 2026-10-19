"""Bounded execution-panel generation and negative controls; no timings/tools."""
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import runpy

import pytest


ROOT = Path(__file__).resolve().parents[3]


@pytest.fixture
def bench(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT/'common/benchmarks'))
    return {name: importlib.import_module('bench.'+name)
            for name in ('coverage', 'commitments', 'library_cases', 'operations')}


def panel(bench, family):
    return [c for c in bench['coverage'].cases() if c.name == family]


def test_execution_panel_is_compact_and_dimensioned(bench):
    counts = Counter(c.name for c in bench['coverage'].cases())
    assert {name: counts[name] for name in ('hash_bytes', 'poseidon', 'merkle', 'host_vector')} == {
        'hash_bytes': 3, 'poseidon': 3, 'merkle': 6, 'host_vector': 4}
    assert len([c for c in panel(bench, 'machine') if 'cpu_height' in c.shape]) == 7
    merkle = [c.shape for c in panel(bench, 'merkle')]
    assert {s['row_width'] for s in merkle if s['height'] == 16} == {1, 8, 9}
    assert {s['height'] for s in merkle if s['row_width'] == 1} == {16, 256}
    assert any(s['height'] == 13 for s in merkle)
    assert {s['opening'] for s in merkle if s['height'] == 256} == {'single', 'multi'}
    for case in bench['coverage'].cases():
        assert case.category and case.mix and case.limitation


def test_sha256_known_answer_empty_and_every_payload_byte(bench, tmp_path):
    for case in panel(bench, 'hash_bytes'):
        program = case.generate(ROOT, tmp_path)
        data = program.inputs[0]['P']
        assert len(data['payload']) == case.shape['payload_bytes']
        assert bytes(data['expected']) == hashlib.sha256(bytes(data['payload'])).digest()
        assert len(data['expected']) == 32
        bad = program.incorrect['P']
        assert bad['payload'] == data['payload']
        assert bad['expected'][1:] == data['expected'][1:]
        assert bad['expected'][0] != data['expected'][0]
    empty = bench['commitments'].hash_bytes({'payload_bytes': 0})
    assert bytes(empty.inputs[0]['P']['expected']).hex() == 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'


def test_poseidon_panel_retains_the_existing_published_answer(bench, tmp_path):
    reference = runpy.run_path(ROOT/'common/tests/kernels/test_poseidon2.py')
    for case in panel(bench, 'poseidon'):
        program = case.generate(ROOT, tmp_path)
        data = program.inputs[0]['P']
        assert list(map(int, data['states'])) == reference['INPUT']*case.shape['states']
        assert list(map(int, data['expected'])) == reference['EXPECTED']*case.shape['states']
        assert program.incorrect['P']['states'] == data['states']
        assert program.incorrect['P']['expected'] != data['expected']
        assert 'one distinct state' in program.oracle


def test_merkle_expected_rows_order_and_canonical_negative(bench, tmp_path):
    for case in panel(bench, 'merkle'):
        program = case.generate(ROOT, tmp_path)
        data = program.inputs[0]['P']
        width, height = int(data['width']), int(data['height'])
        positions = list(map(int, data['positions'])) if 'positions' in data else [int(data['position'])]
        assert len(data['values']) == width*height
        expected = [x for i in positions for x in data['values'][i*width:(i+1)*width]]
        assert data['expected'] == expected
        assert len(expected) == width*case.shape['queries']
        assert data['bad_rows'][1:] == expected[1:]
        assert int(data['bad_rows'][0]) == (int(expected[0])+1) % 2130706433
        if case.shape['opening'] == 'multi':
            assert positions == [height-1, 0, height//2, height//2]
            assert expected[-width:] == expected[-2*width:-width]
        bad = program.incorrect['P']
        assert bad['values'] == data['values'] and bad['bad_rows'] == data['bad_rows']
        assert bad['expected'] != expected
        assert 'same-provider' in program.oracle


def test_large_host_controls_have_matched_linear_inputs_and_bounded_json(bench, tmp_path):
    for n in (16384, 65536):
        cases = [c for c in panel(bench, 'host_vector') if c.shape['elements'] == n]
        programs = {c.shape['operation']: c.generate(ROOT, tmp_path) for c in cases}
        data = {name: program.inputs[0]['P'] for name, program in programs.items()}
        xs = data['length']['xs']
        assert data['sum']['xs'] == xs and len(xs) == n
        assert int(data['length']['expected']) == n
        assert int(data['sum']['expected']) == sum(map(int, xs)) % 2130706433
        for name, program in programs.items():
            # The harness uses indented JSON. Check the actual 16 MiB document
            # and 200,000-node decoder limits, plus the default element ceiling.
            assert len(json.dumps(data[name], indent=2).encode()) + 1 < 16 << 20
            assert len(xs) + 3 < 200000 and len(xs) <= 1 << 16
            assert program.incorrect['P']['xs'] == xs
            assert program.incorrect['P']['expected'] != data[name]['expected']


def test_scaled_machine_inputs_match_program_and_profile(bench, tmp_path):
    for case in panel(bench, 'machine'):
        if 'cpu_height' not in case.shape:
            continue
        program = case.generate(ROOT, tmp_path/case.identifier)
        public, witness = (program.inputs[0][name] for name in ('public', 'witness'))
        shape = case.shape
        assert program.entry == f'accumulator_machine::Proof{shape["reduction"]}'
        assert 'ThreeTableArgument<Machine,R,5,6,8,8>' in program.source
        assert {name: public[name] for name in ('round_count', 'query_count', 'attempt_count', 'channel_count', 'shift')} == {
            'round_count': '5', 'query_count': '8', 'attempt_count': '8', 'channel_count': '2', 'shift': '3'}
        assert int(public['cpu_height']) == int(public['program_height']) == shape['cpu_height']
        assert int(public['memory_height']) == shape['memory_height']
        assert public['memory_present'] is shape['memory_present']
        assert len(witness['cpu']) == 11*shape['cpu_height']
        assert witness['usage'] == ['1']*shape['program_height']
        assert len(witness['cells']) == (5*shape['memory_height'] if shape['memory_present'] else 0)
        assert len(public['schedule']) == 2*shape['memory_height']
        # Independently execute the emitted run and compare every CPU before/
        # after value, program tuple and memory interaction count.
        document = json.loads((tmp_path/case.identifier/'machine-run.json').read_text())
        acc, cells, events = int(document[2]), [0, 0], 0
        for i, (op, text) in enumerate(document[1]):
            value, before = int(text), acc
            if op == 'add-immediate': acc = (acc+value) % 2130706433
            elif op == 'store': cells[value] = acc; events += 1
            elif op == 'load': acc = cells[value]; events += 1
            else: assert op == 'halt' and i == shape['cpu_height']-1
            row = list(map(int, witness['cpu'][11*i:11*(i+1)]))
            assert row[:2] == [i, i] and row[4:6] == [before, acc]
            assert public['instructions'][3*i:3*(i+1)] == list(map(str, [i, row[2], value]))
        assert events == shape['memory_events'] and int(public['final']) == acc
        assert program.changed['final'] != public['final'] and program.mutate_proof is not None
        with pytest.raises(ValueError, match='fixed inputs only'):
            case.generate(ROOT, tmp_path/case.identifier, statement=1)


@pytest.mark.parametrize('height,memory', [(32, 64), (8, 8), (8, 64), (3, 8)])
def test_machine_generation_refuses_unsupported_heights(bench, height, memory):
    with pytest.raises(ValueError):
        bench['library_cases'].machine_run({'cpu_height': height, 'memory_height': memory,
                                           'memory_present': True})


def test_optional_memory_presence_keeps_the_arithmetic_program_fixed(bench, tmp_path):
    cases = {c.identifier: c for c in panel(bench, 'machine')}
    absent = cases['machine-logup-h8-m16-absent'].generate(ROOT, tmp_path/'absent')
    present = cases['machine-logup-h8-m16-present-idle'].generate(ROOT, tmp_path/'present')
    a, p = absent.inputs[0], present.inputs[0]
    for key in ('instructions', 'initial', 'final', 'cpu_height', 'program_height', 'schedule', 'memory_height'):
        assert a['public'][key] == p['public'][key]
    for key in ('cpu', 'usage'):
        assert a['witness'][key] == p['witness'][key]
    assert not a['public']['memory_present'] and p['public']['memory_present']
    assert not a['witness']['cells'] and len(p['witness']['cells']) == 5*16
    assert absent.source == present.source and absent.assets == present.assets
