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
                           compiler_option=[], processes=2, seed=17, cpu=None, threads=1,
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
