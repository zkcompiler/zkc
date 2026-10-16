"""Benchmark evidence controls; these do not assert noisy performance thresholds."""
import importlib
import json
from pathlib import Path
from types import SimpleNamespace
import sys

import pytest


@pytest.fixture
def bench(monkeypatch):
    root = Path(__file__).resolve().parents[3]
    monkeypatch.syspath_prepend(str(root / 'common/benchmarks'))
    return SimpleNamespace(**{name: importlib.import_module(f'bench.{name}')
                              for name in ('io', 'results', 'runner', 'suites')})


def report(plan):
    return {'format': 'zkc.benchmark-worker/0', 'status': 'passed', 'boundary': 'test_call',
            'proof_bytes': 3, 'admission_ns': None, 'process_peak_rss_bytes': None,
            'proofs': [], 'build': {'optimized': True, 'debug_assertions': False}, 'process': {'rayon_num_threads': '1'}, 'timer_floor_ns': 1, 'diagnostics': None,
            'samples': [{'phase': 'warmup' if i < plan['warmups'] else 'sample',
                         'index': i, 'iterations': plan['iterations'], 'elapsed_ns': 100,
                         'cpu_ns': 90, 'first_call_ns': 50}
                        for i in range(plan['samples']+plan['warmups'])]}


@pytest.mark.parametrize('mutation', ['missing', 'phase', 'nan', 'negative', 'zero', 'boundary', 'iterations', 'boolean'])
def test_worker_cannot_silently_change_measurement(bench, mutation):
    plan = {'warmups': 1, 'samples': 2, 'iterations': 3}
    value = report(plan)
    if mutation == 'missing': value['samples'].pop()
    elif mutation == 'phase': value['samples'][0]['phase'] = 'sample'
    elif mutation == 'boundary': value['boundary'] = 'other'
    elif mutation == 'iterations': value['samples'][1]['iterations'] = 1
    else: value['samples'][1]['elapsed_ns'] = {'nan': float('nan'), 'negative': -1, 'zero': 0, 'boolean': True}[mutation]
    with pytest.raises(bench.io.MeasurementError): bench.results.validate_worker(value, plan, 'test_call')


def test_statistics_use_processes_not_pooled_calls(bench):
    plan = {'warmups': 1, 'samples': 3, 'iterations': 1}
    workers = [report(plan), report(plan)]
    for worker, times in zip(workers, ([999999, 10, 20, 1000], [999999, 30, 40, 50])):
        for sample, time in zip(worker['samples'], times): sample.update(elapsed_ns=time, first_call_ns=min(time, 50))
    manifest = {'format': 'zkc.benchmark/0', 'status': 'passed', 'processes': 2, 'plan': plan,
                'matrix': [{'case': 'case', 'implementation': 'impl', 'operation': 'verify', 'boundary': 'test_call'}], 'results': [
        {'case': 'case', 'implementation': 'impl', 'operation': 'verify', 'status': 'passed', 'worker': w, 'repetition': i}
        for i, w in enumerate(workers)]}
    row = bench.results.summarize(manifest)[0]
    assert row['ns_per_call'] == {'min': 20, 'median': 30, 'max': 40, 'mad': 10}
    assert row['process_peak_rss_bytes'] is None
    manifest['status'] = 'failed'
    assert 'ns_per_call' not in bench.results.summarize(manifest)[0]
    manifest['status'] = 'passed'
    manifest['results'].pop()
    with pytest.raises(bench.io.MeasurementError, match='incomplete'):
        bench.results.summarize(manifest)


def test_capture_detects_mid_preparation_and_late_changes(bench, tmp_path):
    source = tmp_path / 'source'
    source.write_text('original')
    capture = bench.runner.Capture(tmp_path / 'snapshot')
    capture.add(source, 'source')
    source.write_text('modified')
    with pytest.raises(bench.io.MeasurementError, match='preparation'): capture.add(source, 'source')
    with pytest.raises(bench.io.MeasurementError, match='during run'): capture.check()
    assert (tmp_path / 'snapshot/source').read_text() == 'original'


def worker(tmp_path, plan, suffix='', response=None):
    path = tmp_path / 'worker'
    path.write_text(f'#!{sys.executable}\nimport json,sys,time\n'
                    f'print(json.dumps({response if response is not None else report(plan)!r}),flush=True)\n'+suffix)
    path.chmod(0o755)
    return path


def arguments(tmp_path):
    return SimpleNamespace(output=tmp_path / 'output', samples=2, warmups=1, iterations=1,
                           processes=2, seed=17, cpu=None, threads=1, label='test', timeout=1)


def prepared(bench, tmp_path, executable, check=lambda *args: None):
    proof = tmp_path / 'valid.proof'
    proof.write_bytes(b'abc')
    def prepare(args, output, capture, manifest):
        capture.add(executable)
        capture.add(proof)
        manifest['contracts'] = {'case': {'protocol': 'test'}}
        jobs = [bench.runner.Job('case', name, 'verify', executable, {}, proof, 'test_call')
                for name in ('left', 'right')]
        return jobs, check
    return prepare


@pytest.mark.parametrize('suffix', ['', 'raise SystemExit(9)', 'time.sleep(10)'])
def test_real_process_journal_and_complete_cell_policy(bench, tmp_path, suffix):
    args = arguments(tmp_path)
    executable = worker(tmp_path, {'samples': 2, 'warmups': 1, 'iterations': 1}, suffix)
    args.timeout = .05 if suffix.startswith('time.sleep') else 1
    code = bench.runner.run(args, prepared(bench, tmp_path, executable))
    manifest = json.loads((args.output / 'manifest.json').read_text())
    assert code == (1 if suffix else 0)
    assert len(manifest['results']) == 4
    assert (args.output / 'plan.json').exists()
    rows = json.loads((args.output / 'summary.json').read_text())['rows']
    assert all(('ns_per_call' in row) == (not suffix) for row in rows)
    assert len(list(args.output.rglob('commands.jsonl'))) == 4
    with pytest.raises(FileExistsError): bench.runner.run(args, prepared(bench, tmp_path, executable))


def test_comparison_rejects_changed_statement_and_host(bench):
    value = completed_manifest()
    assert all(r['current_over_baseline'] == 1 for r in bench.results.compare(value, value)['ratios'])
    for key, changed in [('status', 'failed'), ('contracts', {}), ('host', {}), ('plan', {'samples': 1})]:
        with pytest.raises(bench.io.MeasurementError): bench.results.compare(value, value | {key: changed})


def test_negative_control_catches_accept_all_verifier(bench, tmp_path):
    executable = worker(tmp_path, {'samples': 1, 'warmups': 0, 'iterations': 1})
    job = bench.runner.Job('case', 'reference', 'verify', executable, {'kind': 'schnorr'}, tmp_path/'proof', 'test_call')
    with pytest.raises(bench.io.MeasurementError, match='accepted'):
        bench.suites.refuse(job, tmp_path / 'negative', 1)


def test_fixed_seed_and_thread_environment_are_explicit(bench, tmp_path, monkeypatch):
    monkeypatch.setenv('RAYON_NUM_THREADS', '7')
    args = arguments(tmp_path)
    executable = worker(tmp_path, {'samples': 2, 'warmups': 1, 'iterations': 1})
    schedules = []
    for i in range(2):
        args.output = tmp_path / str(i)
        assert bench.runner.run(args, prepared(bench, tmp_path, executable)) == 0
        schedules.append(json.loads((args.output / 'plan.json').read_text())['schedule'])
    assert schedules[0] == schedules[1]
    import os
    assert os.environ['RAYON_NUM_THREADS'] == '7'


def completed_manifest():
    plan = {'warmups': 0, 'samples': 1, 'iterations': 1}
    matrix = [{'case': 'case', 'implementation': impl, 'operation': 'verify', 'boundary': 'test_call'}
              for impl in ('left', 'right')]
    return {'format': 'zkc.benchmark/0', 'status': 'passed', 'processes': 2, 'plan': plan,
            'matrix': matrix, 'host': {'cpu': 'one'},
            'contracts': {'case': {'boundaries': {'left': 'test_call', 'right': 'test_call'}}},
            'comparisons': [{'case': 'case', 'operation': 'verify', 'numerator': 'left', 'denominator': 'right'}],
            'results': [dict(job, repetition=i, status='passed', worker=report(plan))
                        for job in matrix for i in range(2)]}


@pytest.mark.parametrize('mutation', ['missing', 'duplicate', 'unexpected', 'boundary', 'empty', 'worker-shape', 'unknown'])
def test_saved_success_requires_a_complete_valid_matrix(bench, mutation):
    value = completed_manifest()
    if mutation == 'missing': value['results'].pop()
    elif mutation == 'duplicate': value['results'][1] = value['results'][0]
    elif mutation == 'unexpected': value['results'][0]['implementation'] = 'other'
    elif mutation == 'boundary': value['results'][0]['worker']['boundary'] = 'other'
    elif mutation == 'empty': value['matrix'] = []
    elif mutation == 'worker-shape': value['results'][0]['worker'] = []
    else: value['results'][0]['worker']['samples'][0]['unit'] = 'milliseconds'
    with pytest.raises(bench.io.MeasurementError): bench.results.summarize(value)
    with pytest.raises(bench.io.MeasurementError): bench.results.compare(value, value)


def test_paired_ratios_use_corresponding_processes(bench):
    value = completed_manifest()
    for result, time in zip(value['results'], [100, 1000, 10, 1000], strict=True):
        result['worker']['samples'][0].update(elapsed_ns=time, first_call_ns=time)
    assert bench.results.paired_comparisons(value)[0]['ratio']['median'] == 5.5
    assert 550/505 != 5.5  # Ratio of overall medians is a different statistic.


def test_capture_checks_all_consumed_copies(bench, tmp_path):
    source = tmp_path/'source'
    source.write_text('original')
    capture = bench.runner.Capture(tmp_path/'snapshot')
    capture.add(source, 'first')
    capture.add(source, 'second')
    capture.add(source)
    (tmp_path/'snapshot/first').write_text('modified')
    with pytest.raises(bench.io.MeasurementError, match='captured input changed'): capture.check()


@pytest.mark.parametrize('fault', ['check', 'cached', 'unexpected'])
def test_invalid_produced_proof_invalidates_all_timings(bench, tmp_path, fault):
    args = arguments(tmp_path)
    plan = {'samples': 2, 'warmups': 1, 'iterations': 1}
    executable = tmp_path/'prover'
    executable.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
request=json.loads(Path(sys.argv[1]).read_text())
report={report(plan)!r}
for i in range(3):
    path=Path(request['proof']).with_name(str(i)+'.proof')
    path.write_bytes(bytes([0 if {fault!r} == 'cached' else i])*3)
    report['proofs'].append({{'path': str(path)}})
Path(request['proof']).write_bytes(path.read_bytes())
print(json.dumps(report))
''')
    executable.chmod(0o755)
    def prepare(args, output, capture, manifest):
        manifest['contracts'] = {'case': {'randomized_prover': True}}
        gate = bench.suites.ProofChecks(True)
        def check(job, proof, directory):
            if fault == 'check': raise bench.io.MeasurementError('independent proof rejected')
            if fault == 'unexpected': raise TypeError('unexpected adapter error')
            gate.observe(proof)
        return [bench.runner.Job('case', 'test', 'prove', executable, {}, output/'unused', 'test_call')], check
    assert bench.runner.run(args, prepare) == 1
    manifest = json.loads((args.output/'manifest.json').read_text())
    assert all(r['status'] == 'failed' for r in manifest['results'])
    assert all('ns_per_call' not in row for row in bench.results.summarize(manifest))


@pytest.mark.parametrize('value', [[], None, {'samples': []}])
def test_worker_shape_errors_are_measurement_errors(bench, value):
    with pytest.raises(bench.io.MeasurementError):
        bench.results.validate_worker(value, {'samples': 1, 'warmups': 0, 'iterations': 1}, 'test_call')


@pytest.mark.parametrize('randomized', [True, False])
def test_proof_identity_gate_spans_independent_workers(bench, tmp_path, randomized):
    gate = bench.suites.ProofChecks(randomized)
    first, second = tmp_path/'first', tmp_path/'second'
    first.write_bytes(b'one')
    second.write_bytes(b'one' if randomized else b'two')
    gate.observe(first)
    with pytest.raises(bench.io.MeasurementError): gate.observe(second)


@pytest.mark.parametrize('status', ['rejected', 'input-bounds', 'failed'])
@pytest.mark.parametrize('truncated', [False, True])
def test_negative_gate_requires_structured_rejection(bench, tmp_path, status, truncated):
    executable = tmp_path/'worker'
    value = {'format': 'zkc.benchmark-worker/0', 'status': status, 'error': 'resource limit'}
    executable.write_text(f'#!{sys.executable}\nimport json,sys\nprint(json.dumps({value!r}))\nsys.exit(1)\n')
    executable.chmod(0o755)
    job = bench.runner.Job('case', 'reference', 'verify', executable, {}, tmp_path/'proof', 'test_call')
    if status == 'rejected' or truncated and status == 'input-bounds':
        bench.suites.refuse(job, tmp_path/'negative', 1, truncated=truncated)
    else:
        with pytest.raises(bench.io.MeasurementError, match='outside verification'):
            bench.suites.refuse(job, tmp_path/'negative', 1, truncated=truncated)


def test_pairs_are_adjacent_and_order_alternates(bench, tmp_path):
    args = arguments(tmp_path)
    executable = worker(tmp_path, {'samples': 2, 'warmups': 1, 'iterations': 1})
    assert bench.runner.run(args, prepared(bench, tmp_path, executable)) == 0
    manifest = json.loads((args.output/'manifest.json').read_text())
    assert [i for _, i in manifest['schedule'][:2]] == [i for _, i in reversed(manifest['schedule'][2:])]


@pytest.mark.parametrize('setting', ['threads', 'affinity'])
def test_worker_must_observe_requested_settings(bench, tmp_path, monkeypatch, setting):
    import os
    args = arguments(tmp_path)
    plan = {'samples': 2, 'warmups': 1, 'iterations': 1}
    value = report(plan)
    if setting == 'threads': value['process']['rayon_num_threads'] = '99'
    else:
        args.cpu = 0
        value['process']['affinity'] = None
        monkeypatch.setattr(os, 'sched_getaffinity', lambda pid: {0}, raising=False)
        monkeypatch.setattr(os, 'sched_setaffinity', lambda pid, cpus: None, raising=False)
    executable = worker(tmp_path, plan, response=value)
    assert bench.runner.run(args, prepared(bench, tmp_path, executable)) == 1
    manifest = json.loads((args.output/'manifest.json').read_text())
    assert len(manifest['results']) == 4
    assert all(r['status'] == 'failed' and 'differs' in r['error'] for r in manifest['results'])


@pytest.mark.parametrize('document', [[], {'format': 'zkc.benchmark/0', 'status': 'passed'},
    {'format': 'zkc.benchmark/0', 'status': 'failed', 'results': None},
    {'format': 'zkc.benchmark/0', 'status': 'interrupted', 'results': [], 'matrix': [None]}])
def test_report_rejects_malformed_evidence_before_creating_output(bench, tmp_path, document, capsys):
    from harness import load
    cli = load('benchmark_report_cli', 'common/benchmarks/run.py')
    source = tmp_path/'bad.json'
    source.write_text(json.dumps(document))
    output = tmp_path/'report'
    assert cli.main(['report', str(source), '--output', str(output)]) == 2
    assert not output.exists()
    assert 'Traceback' not in capsys.readouterr().err
