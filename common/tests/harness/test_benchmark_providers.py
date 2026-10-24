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
        for provider in providers.FAMILIES[shape.get('family', 'bls12-381')]:
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
provider=request['backend']['provider']
storage={providers.DIRECT_STORAGE!r}
diagnostics=dict(family='bls12-381',provider=provider,chain_length=1,arithmetic_calls=1,kernel_adapter_conversions=[],bulk_storage=storage[provider],managed=dict(peak_retained_payload_bytes=None,peak_scratch_bytes=None,provider_workspace_admission_bound_bytes_per_call=None))
print(json.dumps(dict(format='zkc.benchmark-worker/0',status='passed',boundary='resident_kernel_call',samples=samples,proof_bytes=0,proofs=[],admission_ns=None,process_peak_rss_bytes=None,build=dict(optimized=True,debug_assertions=False,execution_counts=False),process=dict(rayon_num_threads='1'),timer_floor_ns=1,diagnostics=diagnostics,lifecycle=None)))
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


@pytest.mark.parametrize('provider,boundary', [
    ('arkworks', 'resident'), ('arkworks', 'converted'), ('blst', 'resident'),
    ('blst', 'converted'), ('blst', 'import'), ('blst', 'export'),
])
def test_direct_bls_receipts_validate_provider_storage_and_conversions(modules, provider, boundary):
    providers, _, io = modules
    backend = dict(kind='kernel', provider=provider, group='g1', kernel='scale',
                   elements=1, boundary=boundary)
    conversions = []
    if provider == 'blst' and boundary in ('converted', 'import'):
        conversions = [
            dict(source='group:bls12-381.g1@arkworks.g1/0', target='group:bls12-381.g1@blst/g1',
                 calls=1, elements=1, canonical_payload_bytes=48),
            dict(source='field:bls12-381.fr@arkworks.fr/0', target='field:bls12-381.fr@blst/fr',
                 calls=1, elements=1, canonical_payload_bytes=32),
        ]
    if provider == 'blst' and boundary == 'converted':
        conversions.append(dict(source='group:bls12-381.g1@blst/g1', target='group:bls12-381.g1@arkworks.g1/0',
                                calls=1, elements=1, canonical_payload_bytes=48))
    if provider == 'blst' and boundary == 'export':
        conversions = [dict(source='group:bls12-381.g1@blst/g1', target='group:bls12-381.g1@arkworks.g1/0',
                            calls=1, elements=1, canonical_payload_bytes=48)]
    evidence = dict(family='bls12-381', provider=provider, chain_length=1,
                    arithmetic_calls=0 if boundary in ('import', 'export') else 1,
                    kernel_adapter_conversions=conversions,
                    bulk_storage=providers.DIRECT_STORAGE[provider],
                    managed=dict(peak_retained_payload_bytes=None, peak_scratch_bytes=None,
                                 provider_workspace_admission_bound_bytes_per_call=None))
    providers.validate_evidence(dict(diagnostics=evidence), backend)
    for change in (dict(provider='other'), dict(family='bn254'), dict(chain_length=True),
                   dict(arithmetic_calls=99), dict(bulk_storage=providers.DIRECT_STORAGE[
                       'blst' if provider == 'arkworks' else 'arkworks']),
                   dict(kernel_adapter_conversions=[dict(calls=999)]), dict(managed={})):
        with pytest.raises(io.MeasurementError):
            providers.validate_evidence(dict(diagnostics=evidence | change), backend)
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(dict(diagnostics=None), backend)


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
             if shape.get('family', 'bls12-381') == 'bls12-381'
             and shape['group'] == group and shape['kernel'] == kernel]
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


def test_bn254_catalog_matches_explicit_family_and_provider_inventory(modules):
    providers, _, _ = modules
    shapes = [shape for _, case, shape in providers.catalog() if case.name == 'bn254_provider']
    assert shapes and all(shape['family'] == 'bn254' for shape in shapes)
    for group, kernel, sizes in [('g1', 'msm', (32, 256)), ('g2', 'msm', (32, 256)),
                                 ('pairing', 'pairing_check', (2, 8)), ('scalar', 'field_mul', (1,)),
                                 ('scalar', 'vector_mul', (32, 256)), ('g1', 'scale', (1,)), ('g2', 'scale', (1,)),
                                 ('g1', 'scale_each', (1, 32, 1024)), ('g2', 'scale_each', (1, 32, 1024)),
                                 ('g1', 'vector_scale', (1, 32, 1024)), ('g2', 'vector_scale', (1, 32, 1024))]:
        for n in sizes:
            selected = [shape for shape in shapes if (shape['group'], shape['kernel'], shape['elements']) == (group, kernel, n)]
            assert {s['boundary'] for s in selected} >= {'resident', 'converted', 'installed', 'resident_installed_chain', 'wire_resident_chain'}
            if kernel in ('scale_each', 'vector_scale'):
                assert {(s['boundary'], s.get('chain_length', 1)) for s in selected} == {
                    ('resident', 1), ('converted', 1), ('installed', 1), ('resident', 4),
                    ('converted', 4), ('resident_installed_chain', 4), ('wire_resident_chain', 4)}
    for shape in shapes:
        for provider in ('arkworks', 'halo2curves-axiom'):
            if shape['boundary'] in ('import', 'export') and provider == 'arkworks':
                continue
            providers.validate_backend({'kind': 'kernel', 'provider': provider, **shape},
                                       boundary=providers.BOUNDARIES[shape['boundary']], operation='run')


@pytest.mark.parametrize('family,provider', [
    ('bls12-381', 'halo2curves-axiom'), ('bn254', 'blst'), ('invented', 'arkworks'),
    (None, 'arkworks'), (['bn254'], 'arkworks'), ('bn254', 'halo2curves'),
])
def test_provider_family_requires_positive_compatibility(modules, family, provider):
    providers, _, io = modules
    backend = dict(kind='kernel', family=family, provider=provider, group='g1', kernel='msm', boundary='resident', elements=32)
    with pytest.raises(io.MeasurementError):
        providers.validate_backend(backend)


def test_foreign_bn254_provider_cannot_inherit_the_bls_default(modules):
    providers, _, io = modules
    backend = dict(kind='kernel', provider='halo2curves-axiom', group='g1', kernel='msm', boundary='resident', elements=32)
    with pytest.raises(io.MeasurementError):
        providers.validate_backend(backend)
    providers.validate_backend(backend | dict(provider='blst'))


@pytest.mark.parametrize('group,kernel,inputs,output', [
    ('scalar', 'field_mul', ['field:bn254.fr@halo2curves-axiom/bn254.fr'] * 2,
     'field:bn254.fr@halo2curves-axiom/bn254.fr'),
    ('scalar', 'vector_mul', ['vector:bn254.fr@halo2curves-axiom/bn254.fr'] * 2,
     'vector:bn254.fr@halo2curves-axiom/bn254.fr'),
    ('g1', 'msm', ['vector:bn254.fr@halo2curves-axiom/bn254.fr', 'groups:bn254.g1@halo2curves-axiom/bn254.g1'],
     'group:bn254.g1@halo2curves-axiom/bn254.g1'),
    ('g2', 'msm', ['vector:bn254.fr@halo2curves-axiom/bn254.fr', 'groups:bn254.g2@halo2curves-axiom/bn254.g2'],
     'group:bn254.g2@halo2curves-axiom/bn254.g2'),
    ('g1', 'scale_each', ['vector:bn254.fr@halo2curves-axiom/bn254.fr', 'groups:bn254.g1@halo2curves-axiom/bn254.g1'],
     'groups:bn254.g1@halo2curves-axiom/bn254.g1'),
    ('g2', 'scale_each', ['vector:bn254.fr@halo2curves-axiom/bn254.fr', 'groups:bn254.g2@halo2curves-axiom/bn254.g2'],
     'groups:bn254.g2@halo2curves-axiom/bn254.g2'),
    ('g1', 'vector_scale', ['groups:bn254.g1@halo2curves-axiom/bn254.g1', 'field:bn254.fr@halo2curves-axiom/bn254.fr'],
     'groups:bn254.g1@halo2curves-axiom/bn254.g1'),
    ('g2', 'vector_scale', ['groups:bn254.g2@halo2curves-axiom/bn254.g2', 'field:bn254.fr@halo2curves-axiom/bn254.fr'],
     'groups:bn254.g2@halo2curves-axiom/bn254.g2'),
    ('pairing', 'pairing_check', ['groups:bn254.g1@halo2curves-axiom/bn254.g1', 'groups:bn254.g2@halo2curves-axiom/bn254.g2'],
     'bool@native.bool/0'),
])
def test_bn254_installed_fixture_has_actual_nominal_ports_and_chain(modules, group, kernel, inputs, output):
    providers, _, _ = modules
    backend = dict(kind='kernel', family='bn254', provider='halo2curves-axiom', group=group, kernel=kernel,
                   boundary='resident_installed_chain', elements=1 if kernel == 'field_mul' else 32, chain_length=4)
    program, actual_inputs, outputs, conversions = providers._installed_fixture(backend)
    assert actual_inputs == inputs
    assert outputs == [output] * (4 if group == 'pairing' else 1)
    assert not conversions
    contract = dict(field_mul='field.mul', vector_mul='vector.mul', msm='curve.msm', pairing_check='pairing.check',
                    scale_each='curve.scale_each', vector_scale='curve.vector_scale')[kernel]
    assert program[1][0][3] == f'halo2curves-axiom/resident/{contract}'
    assert len(program[2][0][4]) == (8 if kernel == 'msm' else 5)
    if kernel in ('scale_each', 'vector_scale'):
        calls = program[2][0][4][:-1]
        point_operand = 1 if kernel == 'scale_each' else 0
        for previous, following in zip(calls, calls[1:]):
            assert following[4][point_operand] == previous[5][0]
            assert following[4][1 - point_operand] == calls[0][4][1 - point_operand]


def bn254_report(providers, backend):
    """Synthetic receipts for harness checks; no provider execution is asserted."""
    length = backend.get('chain_length', 1)
    conversions = backend['boundary'] in ('import', 'export')
    bounded = backend['provider'] == 'halo2curves-axiom' and backend['kernel'] in ('msm', 'pairing_check') and not conversions
    evidence = dict(family='bn254', provider=backend['provider'], chain_length=length,
                    arithmetic_calls=0 if conversions else length + (length - 1 if backend['kernel'] == 'msm' else 0),
                    provider_scheduling_work_units_per_arithmetic_call=1000 if bounded else None,
                    managed=dict(peak_retained_payload_bytes=None, peak_scratch_bytes=None,
                                 provider_workspace_admission_bound_bytes_per_call=4096 if bounded else None))
    if backend['boundary'] in ('resident', 'converted', 'import', 'export'):
        evidence['kernel_adapter_conversions'] = providers._direct_conversions(backend)
        evidence['bulk_storage'] = providers.DIRECT_STORAGE[backend['provider']]
    else:
        program, inputs, outputs, conversions = providers._installed_fixture(backend)
        evidence.update(program=program, input_physical_types=inputs, output_physical_types=outputs,
                        explicit_conversions=conversions,
                        trusted_timing_authorization=dict(allow_unspecified_timing=True, allow_variable_time=backend['kernel'] == 'msm'))
        evidence['managed'].update(input_retained_payload_bytes=512, terminal_runner_usage=dict(
            instructions=10, iterations=0, live_values=1, live_retained_payload_bytes=512,
            cumulative_fresh_payload_bytes=1024, logical_bytes=2048))
        tags = {'field:bn254.fr': 40, 'vector:bn254.fr': 41, 'group:bn254.g1': 46,
                'groups:bn254.g1': 47, 'group:bn254.g2': 48, 'groups:bn254.g2': 49, 'bool': 5}
        for name, types in (('input', inputs), ('output', outputs)):
            logical = [ty.split('@')[0] for ty in types]
            evidence[f'{name}_wire_tags'] = [tags[ty] for ty in logical]
            evidence[f'{name}_wire_bytes'] = sum(7 if ty == 'bool' else
                (10 + backend['elements'] * (64 if ty.endswith('.g2') else 32)) if ty.startswith(('groups:', 'vector:'))
                else (70 if ty.endswith('.g2') else 38) for ty in logical)
    return dict(diagnostics=evidence)


@pytest.mark.parametrize('boundary', list(('resident', 'converted', 'import', 'export', 'installed',
                                          'resident_installed_chain', 'wire_resident_chain')))
@pytest.mark.parametrize('group', ['g1', 'g2'])
@pytest.mark.parametrize('kernel', ['msm', 'scale_each', 'vector_scale'])
def test_bn254_evidence_distinguishes_each_conversion_boundary(modules, boundary, group, kernel):
    providers, _, _ = modules
    backend = dict(kind='kernel', family='bn254', provider='halo2curves-axiom', group=group, kernel=kernel,
                   boundary=boundary, elements=32, chain_length=1 if boundary in ('installed', 'import', 'export') else 4)
    report = bn254_report(providers, backend)
    providers.validate_evidence(report, backend)
    conversions = report['diagnostics'].get('kernel_adapter_conversions', report['diagnostics'].get('explicit_conversions'))
    if boundary in ('converted', 'installed', 'import', 'export'):
        points = next(row for row in conversions if row['source'].startswith('groups:'))
        assert points['canonical_payload_bytes'] == 32 * (64 if group == 'g2' else 32)
        assert points['calls'] == (1 if boundary == 'installed' else 32)
        if boundary in ('converted', 'installed', 'import'):
            scalar = next(row for row in conversions if ':bn254.fr@' in row['source'])
            assert scalar['elements'] == (1 if kernel == 'vector_scale' else 32)
            assert scalar['canonical_payload_bytes'] == scalar['elements'] * 32


@pytest.mark.parametrize('provider', ['arkworks', 'halo2curves-axiom'])
@pytest.mark.parametrize('group', ['g1', 'g2'])
@pytest.mark.parametrize('kernel', ['scale_each', 'vector_scale'])
@pytest.mark.parametrize('n', [1, 32, 1024])
@pytest.mark.parametrize('boundary', ['resident', 'converted', 'installed', 'resident_installed_chain', 'wire_resident_chain'])
def test_bn254_bulk_scaling_receipts_preserve_vector_results(modules, provider, group, kernel, n, boundary):
    providers, _, _ = modules
    backend = dict(kind='kernel', family='bn254', provider=provider, group=group, kernel=kernel,
                   boundary=boundary, elements=n, chain_length=1 if boundary == 'installed' else 4)
    report = bn254_report(providers, backend)
    providers.validate_evidence(report, backend)
    evidence = report['diagnostics']
    assert evidence['arithmetic_calls'] == backend['chain_length']
    if boundary in ('installed', 'resident_installed_chain', 'wire_resident_chain'):
        assert evidence['output_physical_types'][0].startswith(f'groups:bn254.{group}@')
        assert evidence['output_wire_tags'] == [49 if group == 'g2' else 47]
        assert evidence['output_wire_bytes'] == 10 + n * (64 if group == 'g2' else 32)
        assert evidence['input_wire_tags'] == ([47 if group == 'g1' else 49, 40]
                                               if kernel == 'vector_scale' else [41, 47 if group == 'g1' else 49])


@pytest.mark.parametrize('kernel', ['scale_each', 'vector_scale'])
@pytest.mark.parametrize('change', [dict(group='scalar'), dict(group='pairing'), dict(elements=0),
                                    dict(elements=True), dict(chain_length=33), dict(boundary='installed', chain_length=4),
                                    dict(provider='arkworks', boundary='import')])
def test_bn254_bulk_scaling_refuses_invalid_shapes(modules, kernel, change):
    providers, _, io = modules
    backend = dict(kind='kernel', family='bn254', provider='halo2curves-axiom', group='g1', kernel=kernel,
                   boundary='resident', elements=32)
    with pytest.raises(io.MeasurementError):
        providers.validate_backend(backend | change)


@pytest.mark.parametrize('kernel', ['scale_each', 'vector_scale'])
@pytest.mark.parametrize('change', [dict(output_wire_tags=[46]), dict(output_wire_bytes=38),
                                    dict(output_physical_types=['group:bn254.g1@halo2curves-axiom/bn254.g1']),
                                    dict(arithmetic_calls=7)])
def test_bn254_bulk_scaling_refuses_single_point_or_msm_receipts(modules, kernel, change):
    providers, _, io = modules
    backend = dict(kind='kernel', family='bn254', provider='halo2curves-axiom', group='g1', kernel=kernel,
                   boundary='wire_resident_chain', elements=32, chain_length=4)
    report = bn254_report(providers, backend)
    report['diagnostics'].update(change)
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(report, backend)


@pytest.mark.parametrize('boundary', ['resident', 'converted', 'wire_resident_chain'])
@pytest.mark.parametrize('field,value', [
    ('family', 'bls12-381'), ('provider', 'blst'), ('arithmetic_calls', 4), ('chain_length', True),
    ('provider_scheduling_work_units_per_arithmetic_call', None),
])
def test_bn254_receipts_refuse_wrong_family_chain_or_work(modules, boundary, field, value):
    providers, _, io = modules
    backend = dict(kind='kernel', family='bn254', provider='halo2curves-axiom', group='g2', kernel='msm',
                   boundary=boundary, elements=32, chain_length=4)
    report = bn254_report(providers, backend)
    report['diagnostics'][field] = value
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(report, backend)


@pytest.mark.parametrize('field,value', [
    ('input_wire_tags', [66, 52]), ('output_wire_tags', [51]), ('input_wire_bytes', 100),
    ('output_wire_bytes', 102), ('input_physical_types', ['field:bls12-381.fr@blst/fr']),
    ('explicit_conversions', [dict(calls=32, elements=32, canonical_payload_bytes=3072)]),
])
def test_bn254_installed_receipts_refuse_bls_frames_ports_and_widths(modules, field, value):
    providers, _, io = modules
    backend = dict(kind='kernel', family='bn254', provider='halo2curves-axiom', group='g2', kernel='msm',
                   boundary='installed', elements=32)
    report = bn254_report(providers, backend)
    report['diagnostics'][field] = value
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(report, backend)


def test_bn254_direct_receipts_do_not_invent_arkworks_conversions_or_native_peaks(modules):
    providers, _, io = modules
    backend = dict(kind='kernel', family='bn254', provider='arkworks', group='scalar', kernel='field_mul',
                   boundary='converted', elements=1, chain_length=4)
    report = bn254_report(providers, backend)
    providers.validate_evidence(report, backend)
    report['diagnostics']['managed']['peak_scratch_bytes'] = True
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(report, backend)


@pytest.mark.parametrize('provider', ['arkworks', 'halo2curves-axiom'])
@pytest.mark.parametrize('group,kernel,n', [('scalar', 'field_mul', 1), ('scalar', 'vector_mul', 32),
                                         ('pairing', 'pairing_check', 2)])
@pytest.mark.parametrize('boundary', ['resident', 'converted', 'installed', 'resident_installed_chain', 'wire_resident_chain'])
def test_bn254_scalar_and_pairing_receipts_keep_family_and_boundary(modules, provider, group, kernel, n, boundary):
    providers, _, _ = modules
    backend = dict(kind='kernel', family='bn254', provider=provider, group=group, kernel=kernel,
                   boundary=boundary, elements=n, chain_length=1 if boundary == 'installed' else 4)
    providers.validate_evidence(bn254_report(providers, backend), backend)


@pytest.mark.parametrize('change', [
    {'peak_scratch_bytes': 100}, {'terminal_runner_usage': {}},
    {'terminal_runner_usage': dict(instructions=1, iterations=0, live_values=0, live_retained_payload_bytes=0,
                                 cumulative_fresh_payload_bytes=0, logical_bytes=True)},
    {'provider_workspace_admission_bound_bytes_per_call': True},
])
def test_bn254_resource_receipts_refuse_invented_peaks_or_missing_charges(modules, change):
    providers, _, io = modules
    backend = dict(kind='kernel', family='bn254', provider='halo2curves-axiom', group='g1', kernel='msm',
                   boundary='wire_resident_chain', elements=32, chain_length=4)
    report = bn254_report(providers, backend)
    report['diagnostics']['managed'].update(change)
    with pytest.raises(io.MeasurementError):
        providers.validate_evidence(report, backend)
