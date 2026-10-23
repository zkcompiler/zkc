"""Provider measurements keep representation boundaries and requests explicit."""
import importlib
import json
from pathlib import Path
from types import SimpleNamespace
import sys

import pytest


@pytest.fixture
def modules(monkeypatch):
    root = Path(__file__).resolve().parents[3]
    monkeypatch.syspath_prepend(str(root / 'common/benchmarks'))
    return tuple(importlib.import_module(f'bench.{name}') for name in ('providers', 'results', 'io'))


def test_provider_catalog_has_matched_complete_and_resident_boundaries(modules):
    providers, results, _ = modules
    names = set()
    for name, case, shape in providers.catalog():
        assert name not in names
        names.add(name)
        for provider in ('arkworks', 'blst'):
            if shape['boundary'] in ('import', 'export') and provider == 'arkworks':
                continue
            results.validate_backend({'kind': 'kernel', 'provider': provider, **shape},
                                     boundary=providers.BOUNDARIES[shape['boundary']])
    for group in ('g1', 'g2'):
        for n in (32, 256, 1024):
            for boundary in ('resident', 'converted', 'installed'):
                assert f'provider-{group}-msm-{boundary}-{n}' in names
            for boundary in ('import', 'export'):
                assert f'provider-{group}-{boundary}-{n}' in names
    assert 'provider-pairing-pairing-check-installed-32' in names


@pytest.mark.parametrize('change', [
    {'provider': 'unknown'}, {'group': 'gt'}, {'elements': True}, {'elements': 0},
    {'elements': 4097}, {'kernel': 'scale', 'elements': 32}, {'extra': 0},
    {'group': 'pairing'}, {'boundary': 'import', 'provider': 'arkworks'},
])
def test_provider_requests_refuse_mismatched_or_unbounded_shapes(modules, change):
    _, results, io = modules
    request = {'kind': 'kernel', 'provider': 'blst', 'group': 'g1', 'kernel': 'msm',
               'elements': 32, 'boundary': 'installed'}
    with pytest.raises(io.MeasurementError):
        results.validate_backend(request | change)
    with pytest.raises(io.MeasurementError):
        results.validate_backend(request, boundary='resident_kernel_call')


def test_provider_controls_publish_complete_paired_reports(modules, tmp_path):
    providers, _, _ = modules
    runner = importlib.import_module('bench.runner')
    worker = tmp_path / 'worker'
    worker.write_text(f'''#!{sys.executable}
import json,sys
request=json.load(open(sys.argv[1]))
plan=request['plan']
samples=[dict(index=i,iterations=plan['iterations'],phase='warmup' if i<plan['warmups'] else 'sample',elapsed_ns=100,cpu_ns=90,first_call_ns=50) for i in range(plan['warmups']+plan['samples'])]
print(json.dumps(dict(format='zkc.benchmark-worker/0',status='passed',boundary='resident_kernel_call',samples=samples,proof_bytes=0,proofs=[],admission_ns=None,process_peak_rss_bytes=None,build=dict(optimized=True,debug_assertions=False,execution_counts=False),process=dict(rayon_num_threads='1'),timer_floor_ns=1,diagnostics=None,lifecycle=None)))
''')
    worker.chmod(0o755)
    args = SimpleNamespace(output=tmp_path / 'output', exclusive=False, samples=1,
                           warmups=0, iterations=1, ingress='json', execution_counts=False,
                           compiler_option=[], processes=2, seed=17, cpus=None, threads=1,
                           label='provider test', timeout=5, worker=worker)
    case = next(case for _, case, shape in providers.catalog()
                if shape == dict(group='g1', kernel='scale', elements=1, boundary='resident'))
    def prepare(args, output, capture, manifest):
        return providers.prepare_case(args, output, capture, manifest, case)
    assert runner.run(args, prepare) == 0
    summary = json.loads((args.output / 'summary.json').read_text())
    assert summary['status'] == 'passed'
    assert len(summary['comparisons']) == 1
    assert summary['comparisons'][0]['boundaries'] == {
        'arkworks': 'resident_kernel_call', 'blst': 'resident_kernel_call'}
    assert 'Arkworks uses existing' in (args.output / 'report.md').read_text()


def test_execution_counts_preset_keeps_source_workloads(modules, monkeypatch, tmp_path):
    suites = importlib.import_module('bench.suites')
    class Prepared(Exception):
        pass
    def captured(*args):
        raise Prepared
    monkeypatch.setattr(suites, 'capture_sources', captured)
    args = SimpleNamespace(case=[], suite=[], preset='execution', execution_counts=True)
    # Reaching preparation establishes that provider controls did not enter the
    # source-only observation preset and trip its preflight refusal.
    with pytest.raises(Prepared):
        suites.prepare(args, tmp_path, None, {})


@pytest.mark.parametrize('group,kernel', [('scalar', 'field_mul'), ('scalar', 'vector_mul'),
                                         ('g1', 'scale'), ('g2', 'msm'), ('pairing', 'pairing_check')])
def test_resident_catalog_retains_repetition_and_full_wire_boundaries(modules, group, kernel):
    providers, results, _ = modules
    cases = [shape for _, _, shape in providers.catalog()
             if shape['group'] == group and shape['kernel'] == kernel]
    for boundary in ('resident_installed_chain', 'wire_resident_chain'):
        selected = [shape for shape in cases if shape['boundary'] == boundary]
        assert selected
        assert all(shape['chain_length'] == 4 for shape in selected)
        for shape in selected:
            results.validate_backend({'kind': 'kernel', 'provider': 'blst', **shape},
                                     boundary=providers.BOUNDARIES[boundary])
    if kernel in ('vector_mul', 'msm'):
        assert {1, 32, 1024} <= {shape['elements'] for shape in cases}


@pytest.mark.parametrize('change', [
    {'chain_length': 0}, {'chain_length': 33}, {'chain_length': True},
    {'chain_length': 4, 'boundary': 'installed'},
    {'group': 'scalar', 'kernel': 'msm'},
    {'group': 'g1', 'kernel': 'vector_mul'},
    {'group': 'scalar', 'kernel': 'vector_mul', 'boundary': 'import'},
])
def test_resident_requests_refuse_invalid_chain_contracts(modules, change):
    _, results, io = modules
    request = {'kind': 'kernel', 'provider': 'blst', 'group': 'scalar',
               'kernel': 'vector_mul', 'elements': 32, 'boundary': 'resident_installed_chain',
               'chain_length': 4}
    with pytest.raises(io.MeasurementError):
        results.validate_backend(request | change)


@pytest.fixture
def resident_evidence():
    return {'diagnostics': {
        'provider': 'blst', 'chain_length': 4, 'arithmetic_calls': 4,
        'trusted_timing_authorization': {'allow_unspecified_timing': True, 'allow_variable_time': False},
        'explicit_conversions': [],
        'input_physical_types': ['field:bls12-381.fr@blst/fr'] * 2,
        'output_physical_types': ['field:bls12-381.fr@blst/fr'],
         'program': ['zkc.program/0',
                    [['b0', 'field.mul', ['bls12-381.fr'], 'blst/resident/field.mul', []]],
                    [['function', 'f', [['a0', 'field:bls12-381.fr@blst/fr'],
                                        ['a1', 'field:bls12-381.fr@blst/fr']],
                      ['field:bls12-381.fr@blst/fr'],
                      [['op', f'site{i}', 'b0', [], ['a0' if i == 0 else f'v{i-1}', 'a1'], [f'v{i}']]
                       for i in range(4)] + [['return', ['v3']]], ['f', []]]],
                    [['participant', 'actor', 'instance', 'P',
                      [['a0', 'field:bls12-381.fr@blst/fr'], ['a1', 'field:bls12-381.fr@blst/fr']],
                      ['field:bls12-381.fr@blst/fr'],
                      [['local', 'work', 'f', ['a0', 'a1'], ['v3']], ['return', ['v3']]], []]],
                    [['entry', 'main', [['P', 'actor']]]]],
        'managed': {'input_retained_payload_bytes': 1024, 'terminal_runner_usage': {},
                    'peak_retained_payload_bytes': None, 'peak_scratch_bytes': None},
        'input_wire_bytes': 66, 'output_wire_bytes': 33}}


def test_resident_evidence_records_selected_codec_and_unknown_managed_peaks(modules, resident_evidence):
    providers, _, _ = modules
    backend = {'kind': 'kernel', 'provider': 'blst', 'group': 'scalar', 'kernel': 'field_mul',
               'boundary': 'wire_resident_chain', 'elements': 1, 'chain_length': 4}
    providers.validate_evidence(resident_evidence, backend)


@pytest.mark.parametrize('field,value', [
    ('provider', 'arkworks'), ('chain_length', 1), ('arithmetic_calls', 1),
    ('trusted_timing_authorization', {'allow_unspecified_timing': True, 'allow_variable_time': True}),
    ('input_physical_types', ['field:bls12-381.fr@arkworks.fr/0']),
    ('managed', {'input_retained_payload_bytes': 10, 'terminal_runner_usage': {}}),
    ('program', ['zkc.program/0', [['b', 'field.mul', ['bls12-381.fr'], 'blst/field.mul', []]], [], [], []]),
    ('explicit_conversions', [{'calls': 1}]),
])
def test_resident_evidence_refuses_fallback_policy_and_missing_observations(modules, resident_evidence, field, value):
    providers, _, io = modules
    backend = {'kind': 'kernel', 'provider': 'blst', 'group': 'scalar', 'kernel': 'field_mul',
               'boundary': 'wire_resident_chain', 'elements': 1, 'chain_length': 4}
    resident_evidence['diagnostics'][field] = value
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(resident_evidence, backend)


@pytest.mark.parametrize('mutation', [
    'functions', 'participants', 'entries', 'invented_output', 'known_output',
    'wrong_operation', 'wrong_link', 'missing_call', 'wrong_chain', 'conversion',
])
def test_retained_provider_program_cannot_contradict_workload(modules, resident_evidence, mutation):
    providers, _, io = modules
    backend = dict(kind='kernel', provider='blst', group='scalar', kernel='field_mul',
                   boundary='wire_resident_chain', elements=1, chain_length=4)
    evidence = resident_evidence['diagnostics']
    program = evidence['program']
    if mutation in ('functions', 'participants', 'entries'):
        program[{'functions': 2, 'participants': 3, 'entries': 4}[mutation]] = []
    elif mutation in ('invented_output', 'known_output'):
        evidence['output_physical_types'] = [
            'field:bls12-381.fr@invented/layout' if mutation == 'invented_output'
            else 'field:bls12-381.fr@arkworks.fr/0']
    elif mutation == 'wrong_operation':
        program[1][0][1:4] = ['field.add', ['bls12-381.fr'], 'blst/resident/field.add']
    elif mutation == 'wrong_link':
        program[3][0][6][0][2] = 'missing'
    elif mutation == 'missing_call':
        del program[2][0][4][1]
    elif mutation == 'wrong_chain':
        program[2][0][4][1][4][0] = 'a0'
    else:
        evidence['explicit_conversions'] = [dict(logical_type='field:bls12-381.fr',
            source='field:bls12-381.fr@blst/fr', target='field:bls12-381.fr@arkworks.fr/0',
            calls=1, elements=1, canonical_payload_bytes=32)]
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(resident_evidence, backend)
