"""Mutations of retained current-worker evidence; no project binaries or file reads."""
from copy import deepcopy
import importlib
import json
from pathlib import Path

import pytest


@pytest.fixture
def evidence(monkeypatch):
    root = Path(__file__).resolve().parents[3]
    monkeypatch.syspath_prepend(str(root/'common/benchmarks'))
    return (importlib.import_module('bench.results'), importlib.import_module('bench.io'),
            json.loads((Path(__file__).parent/'fixtures/benchmark-evidence.json').read_text()))


@pytest.mark.parametrize('name', ['ingress', 'reference'])
def test_current_producer_evidence_needs_no_files(evidence, monkeypatch, name):
    results, _, fixtures = evidence
    # Neither saved report nor compare may open the archived input/proof paths.
    monkeypatch.setattr(Path, 'open', lambda *a, **kw: pytest.fail('structural validation opened a file'))
    document = fixtures[name]
    assert all(row['status'] == 'passed' for row in results.summarize(document))
    assert len(results.compare(document, document)['ratios']) == len(document['matrix'])


@pytest.mark.parametrize('name', ['ingress', 'reference'])
@pytest.mark.parametrize('fault', ['path_missing', 'path_null', 'path_empty', 'path_nul', 'size_missing',
    'size_bool', 'size_negative', 'size_contradiction', 'digest_missing', 'digest_short', 'digest_upper',
    'mtime_missing', 'mtime_bool', 'mtime_negative', 'unknown', 'duplicate_path', 'aliased_path', 'index'])
def test_actual_proof_artifact_mutations_refuse_saved_and_live(evidence, name, fault):
    results, io, fixtures = evidence
    document = fixtures[name]
    result = document['results'][0]
    proofs = result['worker']['proofs']
    p = proofs[-1]
    if fault == 'path_missing': del p['path']
    elif fault == 'path_null': p['path'] = None
    elif fault == 'path_empty': p['path'] = ''
    elif fault == 'path_nul': p['path'] = 'bad\0path'
    elif fault == 'size_missing': del p['bytes']
    elif fault == 'size_bool': p['bytes'] = True
    elif fault == 'size_negative': p['bytes'] = -1
    elif fault == 'size_contradiction': p['bytes'] += 1
    elif fault == 'digest_missing': del p['sha256']
    elif fault == 'digest_short': p['sha256'] = 'a'*63
    elif fault == 'digest_upper': p['sha256'] = 'A'*64
    elif fault == 'mtime_missing': del p['mtime_ns']
    elif fault == 'mtime_bool': p['mtime_ns'] = True
    elif fault == 'mtime_negative': p['mtime_ns'] = -1
    elif fault == 'unknown': p['extra'] = 0
    elif fault == 'duplicate_path': p['path'] = proofs[0]['path']
    elif fault == 'aliased_path': p['path'] = str(Path(proofs[0]['path']).parent/'alias/..'/Path(proofs[0]['path']).name)
    elif name == 'ingress': del p['input_index']
    else: p['input_index'] = 0  # References do not emit Host statement indices.
    with pytest.raises(io.MeasurementError): results.summarize(document)
    with pytest.raises(io.MeasurementError): results.compare(document, document)
    if not fault.startswith('mtime_'):
        for p in proofs: p.pop('mtime_ns', None)
        with pytest.raises(io.MeasurementError):
            results.validate_proof_artifacts(result['worker'], document['plan'], 'prove', name == 'ingress')


@pytest.mark.parametrize('kind', ['host', 'run', 'schnorr', 'sumcheck', 'monero'])
@pytest.mark.parametrize('fault', ['unknown', 'missing', 'wrong_type', 'nested_unknown', 'nested_missing', 'nested_type'])
def test_backend_variant_mutations(evidence, kind, fault):
    results, io, fixtures = evidence
    document = fixtures['ingress']
    job = next(j for j in document['matrix'] if j['backend']['kind'] == ('run' if kind == 'run' else 'host'))
    backend = job['backend']
    if kind not in ('host', 'run'):
        backend = deepcopy(fixtures['reference']['matrix'][0]['backend'])
        backend['kind'] = kind
        if kind in ('schnorr', 'monero'): backend['witness'] = 'witness.json'
    results.validate_backend(backend)
    if fault == 'unknown': backend['extra'] = 1
    elif fault == 'missing': del backend['package' if kind in ('host', 'run') else 'public']
    elif fault == 'wrong_type': backend['sha256' if kind in ('host', 'run') else 'public'] = False
    elif kind == 'host':
        if fault == 'nested_unknown': backend['inputs'][0]['extra'] = 0
        elif fault == 'nested_missing': del backend['inputs'][0]['public']
        else: backend['inputs'][0]['witness'] = []
    elif kind == 'run':
        if fault == 'nested_unknown': backend['arguments'] = {'path': 'input.json'}
        elif fault == 'nested_missing': del backend['accept_role']
        else: backend['arguments'] = ['input.json']
    elif kind in ('schnorr', 'monero'): backend['witness'] = {}
    else: backend['witness'] = None  # Sumcheck has no witness field.
    with pytest.raises(io.MeasurementError): results.validate_backend(backend)
    job['backend'] = backend
    document.update(status='failed', results=[])
    with pytest.raises(io.MeasurementError): results.summarize(document)


@pytest.mark.parametrize('outer', ['failed', 'interrupted', 'running'])
@pytest.mark.parametrize('state', ['passed', 'measured', 'failed'])
def test_partial_matrix_retained_workers_are_checked_without_timings(evidence, tmp_path, outer, state):
    results, io, fixtures = evidence
    document = fixtures['ingress']
    document.update(status=outer, results=document['results'][:1], error='retained diagnostic')
    result = document['results'][0]
    result.update(status=state, error='cell diagnostic')
    if state != 'passed': result.pop('validated_proofs')
    results.publish(tmp_path, document)
    assert all('ns_per_call' not in row and row['status'] == 'failed' for row in results.summarize(document))
    assert 'retained diagnostic' in (tmp_path/'report.md').read_text()
    assert results.paired_comparisons(document) == []
    with pytest.raises(io.MeasurementError): results.compare(document, document)


@pytest.mark.parametrize('outer', ['failed', 'interrupted'])
@pytest.mark.parametrize('fault', ['unknown_worker', 'missing_worker', 'null_worker', 'ingress', 'backend_ingress',
    'missing_artifact', 'sample', 'missing_plan', 'unknown_job', 'proof_count'])
def test_unsuccessful_outer_status_does_not_hide_invalid_retained_workers(evidence, outer, fault):
    results, io, fixtures = evidence
    document = fixtures['ingress']
    document.update(status=outer, results=document['results'][:1])
    result = document['results'][0]
    worker = result['worker']
    if fault == 'unknown_worker': worker['extra'] = 0
    elif fault == 'missing_worker': del result['worker']
    elif fault == 'null_worker': result['worker'] = None
    elif fault == 'ingress': worker['lifecycle']['ingress'] = 'json'
    elif fault == 'backend_ingress': worker['lifecycle']['ingress'] = 'native'
    elif fault == 'missing_artifact': del worker['proofs'][0]['sha256']
    elif fault == 'sample': worker['samples'][0]['elapsed_ns'] = True
    elif fault == 'missing_plan': del document['plan']
    elif fault == 'unknown_job': result['case'] = 'other'
    else: worker['proofs'].pop()
    with pytest.raises(io.MeasurementError): results.summarize(document)


@pytest.mark.parametrize('outer', ['failed', 'interrupted'])
@pytest.mark.parametrize('stage', ['preparation', 'worker', 'measured_without_worker'])
def test_early_failures_remain_reportable(evidence, tmp_path, outer, stage):
    results, io, fixtures = evidence
    document = fixtures['ingress']
    document.update(status=outer, results=[], error='original preparation failure')
    if stage == 'preparation':
        document.pop('matrix')
        document.pop('plan')
    else:
        result = deepcopy(fixtures['reference']['results'][0])
        result.update({k:document['matrix'][0][k] for k in ('case','implementation','operation')})
        result.pop('worker')
        result.update(status='measured' if stage == 'measured_without_worker' else 'failed', error='worker launch failed')
        document['results'] = [result]
    if stage == 'measured_without_worker':
        with pytest.raises(io.MeasurementError): results.summarize(document)
    else:
        results.publish(tmp_path, document)
        assert 'original preparation failure' in (tmp_path/'report.md').read_text()
        if stage == 'worker': assert 'worker launch failed' in (tmp_path/'report.md').read_text()


@pytest.mark.parametrize('reference', [False, True])
@pytest.mark.parametrize('fault', [None, 'unknown', 'missing', 'error_type', 'count_bool', 'refusal_unknown',
                                  'refusal_missing', 'refusal_type', 'preparation_unknown', 'ingress'])
def test_current_negative_reports_preserve_backend_differences(evidence, reference, fault):
    results, io, fixtures = evidence
    report = fixtures['negative_reference' if reference else 'negative_host']
    backend = fixtures['reference' if reference else 'ingress']['matrix'][0]['backend']
    if fault == 'unknown': report['extra'] = 1
    elif fault == 'missing': del report['error']
    elif fault == 'error_type': report['error'] = []
    elif fault == 'count_bool': report['completed_calls'] = True
    elif fault == 'ingress': report['ingress'] = 'wire'
    elif fault and reference: report['preparation'] = {}
    elif fault == 'refusal_unknown': report['refusal']['extra'] = 0
    elif fault == 'refusal_missing': del report['refusal']['stop']
    elif fault == 'refusal_type': report['refusal']['code'] = []
    elif fault == 'preparation_unknown': report['preparation']['extra'] = 0
    kwargs = {} if reference else {'completed': 1, 'classes': {'verification'}}
    if fault is None: results.validate_negative_report(report, backend, **kwargs)
    else:
        with pytest.raises(io.MeasurementError): results.validate_negative_report(report, backend, **kwargs)


def test_monero_negative_shape_and_optional_backend_fields(evidence):
    results, io, fixtures = evidence
    # The external C++ worker's failure() emits exactly these three fields.
    report = {k:fixtures['negative_reference'][k] for k in ('format', 'status', 'error')}
    backend = {'kind': 'monero', 'public': 'public.json'}
    results.validate_backend(backend)
    results.validate_negative_report(report, backend)
    with pytest.raises(io.MeasurementError): results.validate_negative_report(report | {'ingress': None}, backend)
    for kind in ('schnorr', 'monero'):
        results.validate_backend(backend | {'kind': kind, 'witness': 'witness.json'})
    results.validate_backend(backend | {'kind': 'schnorr', 'witness': None})
    with pytest.raises(io.MeasurementError): results.validate_backend(backend | {'witness': None})
    host = fixtures['ingress']['matrix'][0]['backend']
    host.pop('preparation_entries')
    host.pop('preparation_bytes')
    for record in host['inputs']:
        record['witness'] = record['proof'] = None
    results.validate_backend(host)


@pytest.mark.parametrize('kind,field', [
    ('host', field) for field in ('kind', 'ingress', 'package', 'sha256', 'inputs', 'preparation')
] + [('run', field) for field in ('kind', 'ingress', 'package', 'sha256', 'arguments', 'accept_role')]
  + [('sumcheck', 'public'), ('schnorr', 'public'), ('monero', 'public')])
def test_every_required_backend_field_is_required(evidence, kind, field):
    results, io, fixtures = evidence
    document = fixtures['ingress' if kind in ('host', 'run') else 'reference']
    job = next(j for j in document['matrix'] if j['backend']['kind'] == (kind if kind in ('host', 'run') else 'sumcheck'))
    job['backend']['kind'] = kind
    del job['backend'][field]
    with pytest.raises(io.MeasurementError): results.summarize(document)


@pytest.mark.parametrize('field,value', [
    ('inputs', []), ('inputs', [{}]), ('inputs', [None]), ('preparation', None), ('preparation', 1),
    ('preparation_entries', True), ('preparation_bytes', -1), ('preparation_entries', 1 << 64),
    ('preparation_bytes', '128'), ('package', ''), ('sha256', 'not a digest'),
])
def test_host_backend_value_types(evidence, field, value):
    results, io, fixtures = evidence
    document = fixtures['ingress']
    document['matrix'][0]['backend'][field] = value
    with pytest.raises(io.MeasurementError): results.summarize(document)


@pytest.mark.parametrize('field,value', [
    ('arguments', {}), ('arguments', None), ('arguments', ''),
    ('accept_role', []), ('accept_role', ''),
])
def test_function_backend_argument_and_result_selection(evidence, field, value):
    results, io, fixtures = evidence
    document = fixtures['ingress']
    document['matrix'][-1]['backend'][field] = value
    with pytest.raises(io.MeasurementError): results.summarize(document)


@pytest.mark.parametrize('fault', ['unknown', 'missing_digest', 'missing_path', 'duplicate', 'worker_mtime'])
def test_live_runner_uses_structural_proof_validator(evidence, monkeypatch, tmp_path, fault):
    results, io, fixtures = evidence
    runner = importlib.import_module('bench.runner')
    document = fixtures['ingress']
    job = document['matrix'][0]
    worker = document['results'][0]['worker']
    # Return an actual complete Host report with live producer artifact fields.
    run_directory = tmp_path/'run'
    for i, p in enumerate(worker['proofs']):
        p.pop('mtime_ns')
        p['path'] = str(run_directory/f'{i}.proof')
    p = worker['proofs'][-1]
    if fault == 'unknown': p['extra'] = 0
    elif fault == 'missing_digest': del p['sha256']
    elif fault == 'missing_path': del p['path']
    elif fault == 'duplicate': p['path'] = worker['proofs'][0]['path']
    else: p['mtime_ns'] = 1  # A worker may not forge runner capture metadata.
    monkeypatch.setattr(runner, 'read_report', lambda record: worker)
    monkeypatch.setattr(runner.Journal, 'command', lambda *args, **kwargs: {'wall_seconds': 0.01})
    # No artifact reads are needed for these structural refusals.
    monkeypatch.setattr(Path, 'is_file', lambda self: True)
    monkeypatch.setattr(Path, 'stat', lambda self, **kw: type('Stat', (), {'st_size': worker['proof_bytes']})())
    worker_job = runner.Job(job['case'], job['implementation'], job['operation'], tmp_path/'unused',
                            job['backend'], tmp_path/'unused.proof', job['boundary'])
    with pytest.raises(io.MeasurementError): runner.execute_job(worker_job, run_directory, document['plan'], 1)
