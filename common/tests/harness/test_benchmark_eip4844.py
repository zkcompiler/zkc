"""The external comparison owns workload and boundary checks, not execution."""
import importlib
from pathlib import Path

import pytest


@pytest.fixture
def modules(monkeypatch):
    monkeypatch.syspath_prepend(str(Path(__file__).resolve().parents[2]/'benchmarks'))
    return {name: importlib.import_module(f'bench.{name}') for name in ('eip4844', 'results', 'io')}


def test_blob_panel_is_distinct_canonical_and_full_width(modules):
    eip = modules['eip4844']
    first, second = eip.blob(0), eip.blob(1)
    assert first != second
    assert first == eip.blob(0)
    for data in (first, second):
        assert len(data) == 4096*32
        values = [int.from_bytes(data[i:i+32], 'big') for i in range(0, len(data), 32)]
        assert all(0 <= value < eip.MODULUS for value in values)
        assert max(values).bit_length() == 255
    cases = [case for _, case, _ in eip.catalog()]
    assert {c.api for c in cases} == {'commitment', 'opening', 'point', 'blob', 'batch'}
    assert [c.count for c in cases if c.api == 'batch'] == [1, 4, 16]


def test_reference_backend_refuses_unknown_fields_and_wrong_boundary(modules):
    results, error = modules['results'], modules['io'].MeasurementError
    backend = {'kind': 'c_kzg', 'api': 'batch', 'setup': '/setup', 'inputs': '/inputs'}
    results.validate_backend(backend, boundary='reference_kzg_call')
    for changed in (backend | {'api': 'other'}, backend | {'threads': 8},
                    {k: v for k, v in backend.items() if k != 'setup'}):
        with pytest.raises(error):
            results.validate_backend(changed)
    with pytest.raises(error):
        results.validate_backend(backend, boundary='admitted_entry_call')
    for api, operation in [('point', 'prove'), ('commitment', 'verify'), ('blob', 'run')]:
        with pytest.raises(error):
            results.validate_backend(backend | {'api': api}, operation=operation)
    with pytest.raises(error):
        results.validate_backend(backend, operation='prove')


@pytest.mark.parametrize('change', ['api', 'count', 'precompute', 'proof_size', 'contract', 'contract_boolean'])
def test_reference_receipts_must_match_the_declared_workload(modules, change):
    results = modules['results']
    backend = {'kind': 'c_kzg', 'api': 'batch'}
    worker = {'diagnostics': {'api': 'batch', 'blob_count': 4, 'precompute': 0}, 'proof_bytes': 4*48}
    contract = {'api': 'batch', 'blobs': 4}
    results.validate_reference(worker, backend, 'verify', contract)
    if change == 'api': worker['diagnostics']['api'] = 'blob'
    elif change == 'count': worker['diagnostics']['blob_count'] = 1
    elif change == 'precompute': worker['diagnostics']['precompute'] = 1
    elif change == 'proof_size': worker['proof_bytes'] -= 1
    elif change == 'contract_boolean':
        worker['diagnostics']['blob_count'], worker['proof_bytes'], contract['blobs'] = 1, 48, True
    else: contract['blobs'] = 16
    with pytest.raises(modules['io'].MeasurementError):
        results.validate_reference(worker, backend, 'verify', contract)


def test_function_result_checks_have_one_current_shape(modules):
    results, error = modules['results'], modules['io'].MeasurementError
    backend = {'kind': 'run', 'package': '/package', 'sha256': 'a'*64,
               'arguments': '/arguments', 'ingress': 'json',
               'check': {'kind': 'output', 'expected': '/expected'}}
    results.validate_backend(backend, boundary='admitted_function_call')
    for check in ({'kind': 'output'}, {'kind': 'output', 'expected': '/expected', 'role': 'P'},
                  {'kind': 'acceptance'}, {'kind': 'other'}):
        with pytest.raises(error):
            results.validate_backend(backend | {'check': check})
    with pytest.raises(error):
        results.validate_backend(backend | {'accept_role': 'P'})
