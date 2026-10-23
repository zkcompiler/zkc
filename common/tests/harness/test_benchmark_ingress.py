"""Ingress policy and attribution through the maintained scheduler and readers."""
from copy import deepcopy
import importlib
import importlib.util
import json
from pathlib import Path
import sys

import pytest

from test_benchmark_coverage import lifecycle_worker

ROOT = Path(__file__).resolve().parents[3]
PLAN = {'warmups': 2, 'samples': 2, 'iterations': 1}


@pytest.fixture
def modules(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT/'common/benchmarks'))
    return {name: importlib.import_module(f'bench.{name}') for name in ('io', 'runner', 'results')}


def preowned(policy):
    report = lifecycle_worker()
    report['lifecycle'].update(ingress=policy, input_setup=[
        {'input_index': i, 'construction_ns': (i+1)*101, 'retained_payload_bytes': (i+1)*4096}
        for i in range(2)])
    for call in report['lifecycle']['calls']:
        call.update(decode_ns=None, request_ns=3)
    return report


def saved_host_manifest(policy='json', operation='prove', inputs=2, iterations=1):
    worker = lifecycle_worker() if policy == 'json' else preowned(policy)
    plan = PLAN | {'iterations': iterations}
    for sample in worker['samples']:
        sample['iterations'] = iterations
    life = worker['lifecycle']
    life['input_setup'] = life['input_setup'][:inputs]
    life['calls'] = [deepcopy(call) for call in life['calls'] for _ in range(iterations)]
    for index, call in enumerate(life['calls']):
        call['input_index'] = index % inputs
    worker['proofs'] = [dict(path=f'/retained/{index}.proof', bytes=4, sha256='0'*64, mtime_ns=1, input_index=call['input_index'])
                        for index, call in enumerate(life['calls'])] if operation == 'prove' else []
    job = dict(case='case', implementation='zkc', operation=operation, boundary='admitted_entry_call',
               backend=dict(kind='host', package='entry.zkpkg', sha256='0'*64, ingress=policy, inputs=[{'public': f'{i}-public.json'} for i in range(inputs)], preparation=True))
    return dict(format='zkc.benchmark/0', ingress=policy, status='passed', observation='timing',
                compiler_options=[], processes=1, plan=plan, matrix=[job], contracts={}, threads=1,
                host={'requested_cpus': None, 'affinity': None},
                results=[dict(case='case', implementation='zkc', operation=operation, status='passed',
                              repetition=0, worker=worker, validated_proofs=len(worker['proofs']))])


def assert_report_refused(modules, tmp_path, document, capsys):
    from harness import load
    cli = load('benchmark_ingress_report_cli', 'common/benchmarks/run.py')
    source = tmp_path/'manifest.json'
    source.write_text(json.dumps(document))
    output = tmp_path/'report'
    assert cli.main(['report', str(source), '--output', str(output)]) == 2
    assert not output.exists()
    assert 'Traceback' not in capsys.readouterr().err


@pytest.mark.parametrize('kind', ['host', 'run'])
@pytest.mark.parametrize('fault', ['absent_backend', 'null_backend', 'array_backend', 'missing_kind',
                                  'unknown_kind', 'missing_ingress', 'unknown_ingress',
                                  'substituted_ingress', 'wrong_kind', 'wrong_boundary'])
def test_failed_report_checks_declared_backends_before_output(modules, tmp_path, capsys, kind, fault):
    document = saved_host_manifest(operation='verify')
    document.update(status='failed', results=[])
    job = document['matrix'][0]
    job.update(boundary='admitted_entry_call' if kind == 'host' else 'admitted_function_call')
    job['backend']['kind'] = kind
    if fault == 'absent_backend': del job['backend']
    elif fault == 'null_backend': job['backend'] = None
    elif fault == 'array_backend': job['backend'] = []
    elif fault == 'missing_kind': del job['backend']['kind']
    elif fault == 'unknown_kind': job['backend']['kind'] = 'other'
    elif fault == 'missing_ingress': del job['backend']['ingress']
    elif fault == 'wrong_kind': job['backend']['kind'] = 'schnorr'
    elif fault == 'wrong_boundary': job['boundary'] = 'reference_call'
    else: job['backend']['ingress'] = 'all' if fault == 'unknown_ingress' else 'prepared'
    with pytest.raises(modules['io'].MeasurementError):
        modules['results'].summarize(document)
    assert_report_refused(modules, tmp_path, document, capsys)


@pytest.mark.parametrize('matrix', ['absent', 'empty', 'declared'])
def test_failed_preparation_can_be_reported_without_a_matrix(modules, tmp_path, matrix):
    from harness import load
    document = saved_host_manifest(operation='verify')
    document.update(status='failed', results=[])
    if matrix == 'absent': del document['matrix']
    elif matrix == 'empty': document['matrix'] = []
    source = tmp_path/'manifest.json'
    source.write_text(json.dumps(document))
    cli = load('benchmark_ingress_failed_report_cli', 'common/benchmarks/run.py')
    output = tmp_path/'report'
    assert cli.main(['report', str(source), '--output', str(output)]) == 0
    rows = json.loads((output/'summary.json').read_text())['rows']
    assert len(rows) == (1 if matrix == 'declared' else 0)
    assert all(row['status'] == 'failed' and 'ns_per_call' not in row for row in rows)


@pytest.mark.parametrize('policy', ['json', 'wire', 'native', 'prepared'])
@pytest.mark.parametrize('inputs,iterations', [(2, 1), (1, 3)])
def test_saved_prover_requires_all_validated_proofs_in_statement_order(modules, policy, inputs, iterations):
    document = saved_host_manifest(policy, inputs=inputs, iterations=iterations)
    assert modules['results'].summarize(document)[0]['status'] == 'passed'
    assert len(modules['results'].compare(document, document)['ratios']) == 1


@pytest.mark.parametrize('fault', ['empty', 'missing_proof', 'extra_proof', 'missing_validated',
                                  'zero_validated', 'short_validated', 'boolean_validated', 'string_validated',
                                  'missing_index', 'boolean_index', 'wrong_index', 'reordered',
                                  'missing_statement', 'extra_statement', 'artifact_shape', 'wrong_boundary'])
def test_saved_prover_corruption_refuses_before_output(modules, tmp_path, capsys, fault):
    document = saved_host_manifest('prepared')
    result = document['results'][0]
    proofs = result['worker']['proofs']
    if fault == 'empty': proofs.clear()
    elif fault == 'missing_proof': proofs.pop()
    elif fault == 'extra_proof': proofs.append(deepcopy(proofs[-1]))
    elif fault == 'missing_validated': del result['validated_proofs']
    elif fault == 'zero_validated': result['validated_proofs'] = 0
    elif fault == 'short_validated': result['validated_proofs'] -= 1
    elif fault == 'boolean_validated': result['validated_proofs'] = True
    elif fault == 'string_validated': result['validated_proofs'] = '4'
    elif fault == 'missing_index': del proofs[0]['input_index']
    elif fault == 'boolean_index': proofs[1]['input_index'] = True
    elif fault == 'wrong_index': proofs[0]['input_index'] = 1
    elif fault == 'reordered': proofs.reverse()
    elif fault == 'artifact_shape': proofs[0] = None
    elif fault == 'wrong_boundary':
        document['matrix'][0]['boundary'] = result['worker']['boundary'] = 'reference_call'
    elif fault == 'extra_statement': document['matrix'][0]['backend']['inputs'].append({})
    else:
        # Internally consistent proofs/calls still cannot omit a captured statement.
        for proof, call in zip(proofs, result['worker']['lifecycle']['calls'], strict=True):
            proof['input_index'] = call['input_index'] = 0
        result['worker']['lifecycle']['input_setup'].pop()
    with pytest.raises(modules['io'].MeasurementError):
        modules['results'].summarize(document)
    with pytest.raises(modules['io'].MeasurementError):
        modules['results'].compare(document, document)
    assert_report_refused(modules, tmp_path, document, capsys)


@pytest.mark.parametrize('policy', [None, 'json', 'wire', 'native', 'prepared'])
def test_cli_selects_one_condition_and_defaults_to_json(modules, monkeypatch, tmp_path, policy):
    spec = importlib.util.spec_from_file_location('benchmark_cli_ingress', ROOT/'common/benchmarks/run.py')
    cli = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cli)
    selected = []
    monkeypatch.setattr(cli, 'run', lambda args, prepare: selected.append(args.ingress) or 0)
    argv = ['run', '--compiler', sys.executable, '--runtime', sys.executable,
            '--worker', sys.executable, '--output', str(tmp_path/'output')]
    assert cli.main(argv + (['--ingress', policy] if policy else [])) == 0
    assert selected == [policy or 'json']
    with pytest.raises(SystemExit):
        cli.main(argv + ['--ingress', 'both'])


@pytest.mark.parametrize('policy', ['wire', 'native', 'prepared'])
def test_existing_scheduler_preserves_ingress_and_statement_setup(modules, tmp_path, policy):
    response = preowned(policy)
    executable = tmp_path/'worker'
    executable.write_text(f'#!{sys.executable}\nimport json\nprint(json.dumps({response!r}))\n')
    executable.chmod(0o755)
    backend = {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': policy, 'inputs': [{'public': 'first'}, {'public': 'second'}],
               'preparation': True}
    job = modules['runner'].Job('unchanged-case', 'zkc', 'verify', executable, backend,
                               tmp_path/'proof', 'admitted_entry_call')
    result = modules['runner'].execute_job(job, tmp_path/'run', PLAN, 5)
    request = json.loads((tmp_path/'run/request.json').read_text())
    assert request['backend'] == backend
    assert [call['input_index'] for call in result['worker']['lifecycle']['calls']] == [0, 1, 0, 1]
    row = modules['results'].summarize_lifecycle([result], PLAN)
    assert row['ingress'] == policy and row['decode_ns_per_call'] is None
    assert row['request_ns_per_call']['median'] == 3
    assert [s['construction_ns']['median'] for s in row['input_setup']] == [101, 202]
    assert [s['retained_payload_bytes']['median'] for s in row['input_setup']] == [4096, 8192]
    assert [s['first_visit_ns']['median'] for s in row['inputs']] == [10, 100]
    assert [s['ns_per_call']['median'] for s in row['inputs']] == [30, 300]


@pytest.mark.parametrize('fault', ['missing_policy', 'unknown_policy', 'missing_request', 'json_decode',
                                  'setup_missing', 'setup_index', 'setup_extra', 'setup_boolean',
                                  'setup_unknown', 'call_unknown', 'request_boolean'])
def test_ingress_schema_refuses_ambiguous_or_incomplete_attribution(modules, fault):
    report = preowned('prepared')
    life = report['lifecycle']
    if fault == 'missing_policy': del life['ingress']
    elif fault == 'unknown_policy': life['ingress'] = 'all'
    elif fault == 'missing_request': del life['calls'][0]['request_ns']
    elif fault == 'json_decode': life['calls'][0]['decode_ns'] = 3
    elif fault == 'setup_missing': life['input_setup'].pop()
    elif fault == 'setup_index': life['input_setup'][1]['input_index'] = 0
    elif fault == 'setup_extra': life['input_setup'].append(life['input_setup'][1])
    elif fault == 'setup_boolean': life['input_setup'][0]['retained_payload_bytes'] = True
    elif fault == 'setup_unknown': life['input_setup'][0]['extra'] = 3
    elif fault == 'request_boolean': life['calls'][0]['request_ns'] = True
    else: life['calls'][0]['unknown'] = 3
    with pytest.raises(modules['io'].MeasurementError):
        modules['results'].validate_worker(report, PLAN, 'admitted_entry_call')


def test_json_has_decode_observation_and_no_preowned_setup(modules):
    report = lifecycle_worker()
    modules['results'].validate_worker(report, PLAN, 'admitted_entry_call')
    for mutation in ('setup', 'decode'):
        changed = deepcopy(report)
        if mutation == 'setup': changed['lifecycle']['input_setup'] = preowned('wire')['lifecycle']['input_setup']
        else: changed['lifecycle']['calls'][0]['decode_ns'] = None
        with pytest.raises(modules['io'].MeasurementError):
            modules['results'].validate_worker(changed, PLAN, 'admitted_entry_call')


@pytest.mark.parametrize('policy', ['wire', 'native', 'prepared'])
def test_worker_cannot_substitute_a_different_ingress_condition(modules, tmp_path, policy):
    report = preowned(policy)
    executable = tmp_path/'worker'
    executable.write_text(f'#!{sys.executable}\nimport json\nprint(json.dumps({report!r}))\n')
    executable.chmod(0o755)
    backend = {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': True}
    job = modules['runner'].Job('case', 'zkc', 'verify', executable, backend,
                               tmp_path/'proof', 'admitted_entry_call')
    with pytest.raises(modules['io'].MeasurementError, match='ingress differs'):
        modules['runner'].execute_job(job, tmp_path/'run', PLAN, 5)


def test_preowned_report_retains_attribution_without_a_decode_label(modules, tmp_path):
    backend = {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'prepared', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': True}
    job = dict(case='case', implementation='zkc', operation='verify', boundary='admitted_entry_call', backend=backend)
    manifest = dict(format='zkc.benchmark/0', ingress='prepared', status='passed', observation='timing',
                    compiler_options=[], processes=1, plan=PLAN, matrix=[job], contracts={},
                    threads=1, host={'requested_cpus': None, 'affinity': None},
                    results=[job | {'status': 'passed', 'repetition': 0, 'worker': preowned('prepared')}])
    modules['results'].publish(tmp_path, manifest)
    rows = json.loads((tmp_path/'summary.json').read_text())['rows']
    assert rows[0]['decode_ns_per_call'] is None and rows[0]['ingress'] == 'prepared'
    assert len(rows[0]['input_setup']) == 2
    assert 'Preowned input construction' in (tmp_path/'report.md').read_text()
    assert 'prepared' in (tmp_path/'summary.csv').read_text()
    changed = deepcopy(manifest)
    changed['ingress'] = 'wire'
    with pytest.raises(modules['io'].MeasurementError, match='ingress differs'):
        modules['results'].validate_manifest(changed)


@pytest.mark.parametrize('policy', ['json', 'wire', 'native', 'prepared'])
def test_proof_jobs_and_existing_correctness_controls_share_the_selector(modules, monkeypatch, tmp_path, policy):
    from dataclasses import replace
    from types import SimpleNamespace
    execution = importlib.import_module('bench.execution')
    observed, refused = [], []

    def execute(job, directory, plan, timeout):
        observed.append(job)
        directory.mkdir(parents=True)
        proof = directory/'proof.bin'
        proof.write_bytes(job.backend['inputs'][0]['public'].encode())
        return {'proof': {'path': str(proof)}}

    monkeypatch.setattr(execution, 'execute_job', execute)
    monkeypatch.setattr(execution, 'refuse', lambda job, *args, **kwargs: refused.append(job))
    args = SimpleNamespace(worker=tmp_path/'worker', timeout=5, preparation='both',
                           preparation_entries=None, preparation_bytes=None, execution_counts=False)
    files = [{'public': f'public-{i}', 'witness': f'witness-{i}'} for i in range(2)]
    base = {'package': 'same-package', 'sha256': 'same-pin', 'ingress': policy}
    program = SimpleNamespace(changed={'statement': 'changed'}, invalid_witness=None,
                              mutate_proof=lambda proof: proof+b'changed')
    capture = modules['runner'].Capture(tmp_path/'capture')
    jobs, check = execution.proof_jobs(args, capture, tmp_path, 'same-case', base, files, program, 'zkc.framed/0')
    assert {(j.implementation, j.operation) for j in jobs} == {
        ('zkc', 'prove'), ('zkc', 'verify'), ('unprepared', 'prove'), ('unprepared', 'verify')}
    assert all(j.case == 'same-case' and j.backend['ingress'] == policy for j in [*jobs, *observed, *refused])
    assert [j.backend['inputs'][0]['public'] for j in observed[:2]] == ['public-0', 'public-1']
    assert all(j.backend['inputs'] == files for j in jobs)
    # Post-worker proof validation keeps its exact original statement even
    # though the measured worker cycled both statements.
    check(replace(jobs[0], operation='verify'), Path(files[1]['proof']), tmp_path/'check', 1)
    assert observed[-1].backend['inputs'] == [files[1]]
    assert {len(j.backend['inputs']) for j in refused} == {1, 2}


@pytest.mark.parametrize('policy', ['json', 'wire', 'native', 'prepared'])
def test_run_case_and_incorrect_result_gate_keep_identity_and_ingress(modules, monkeypatch, tmp_path, policy):
    from types import SimpleNamespace
    execution = importlib.import_module('bench.execution')
    directory = tmp_path/'case'
    directory.mkdir()
    package = directory/'entry.zkpkg'
    package.write_bytes(b'package')
    monkeypatch.setattr(execution, 'compile_program', lambda *args: (directory, package))
    jobs, negative = [], []
    monkeypatch.setattr(execution, 'execute_job', lambda job, *args: jobs.append(job))

    class Journal:
        def __init__(self, *args): pass
        def command(self, argv, **kwargs):
            negative.append(json.loads(Path(argv[1]).read_text()))
            report = directory/'incorrect.json'
            report.write_text(json.dumps({'status': 'incorrect-result', 'ingress': policy}))
            return {'returncode': 1, 'stdout': str(report)}

    monkeypatch.setattr(execution, 'Journal', Journal)
    program = SimpleNamespace(proof=False, inputs=[{'P': {'expected': True}}], assets={},
                              incorrect={'P': {'expected': False}}, source='same source', oracle='same oracle')
    case = SimpleNamespace(identifier='same-case', name='same', category='control', shape={}, mix={},
                           limitation='bounded', generate=lambda *args, **kwargs: program)
    args = SimpleNamespace(source=ROOT, worker=tmp_path/'worker', ingress=policy, timeout=5, execution_counts=False)
    manifest = {'contracts': {}, 'checks': []}
    selected, _ = execution.prepare_case(args, tmp_path, modules['runner'].Capture(tmp_path/'capture'), manifest, case)
    assert selected == jobs and selected[0].case == 'same-case'
    assert selected[0].backend['ingress'] == negative[0]['backend']['ingress'] == policy
    assert manifest['contracts']['same-case']['ingress_policy'] == policy
    assert negative[0]['backend']['arguments'] != selected[0].backend['arguments']


@pytest.mark.parametrize('policy', ['json', 'wire', 'native', 'prepared'])
def test_run_worker_uses_one_statement_and_the_same_report_contract(modules, tmp_path, policy):
    report = lifecycle_worker() if policy == 'json' else preowned(policy)
    report.update(boundary='admitted_function_call', proof_bytes=0)
    life = report['lifecycle']
    life['preparation_limits'] = None
    life['input_setup'] = life['input_setup'][:1]
    for call in life['calls']:
        call['input_index'] = 0
        del call['preparation']
    executable = tmp_path/'worker'
    executable.write_text(f'#!{sys.executable}\nimport json\nprint(json.dumps({report!r}))\n')
    executable.chmod(0o755)
    job = modules['runner'].Job('same-run-case', 'zkc', 'run', executable,
        {'kind': 'run', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': policy, 'arguments': 'captured', 'check': {'kind': 'acceptance', 'role': 'P'}},
        tmp_path/'unused', 'admitted_function_call')
    result = modules['runner'].execute_job(job, tmp_path/'run', PLAN, 5)
    assert result['worker']['lifecycle']['ingress'] == policy
    assert [call['input_index'] for call in life['calls']] == [0, 0, 0, 0]


@pytest.mark.parametrize('reported', [None, 'json', 'prepared'])
def test_negative_control_requires_its_selected_ingress(modules, tmp_path, reported):
    life = lifecycle_worker()['lifecycle']
    response = dict(format='zkc.benchmark-worker/0', status='rejected', ingress=reported,
                    completed_calls=0, error='proof rejected', refusal={'class': 'verification', 'code': 'artifact-rejected', 'stop': None},
                    preparation_limits=life['preparation_limits'],
                    preparation={phase: dict(entries=0, retained_bytes=0, hits=0) for phase in ('before', 'after')})
    executable = tmp_path/'worker'
    executable.write_text(f'#!{sys.executable}\nimport json,sys\nprint(json.dumps({response!r}))\nsys.exit(1)\n')
    executable.chmod(0o755)
    job = modules['runner'].Job('case', 'zkc', 'verify', executable,
        {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'prepared', 'inputs': [{'public': 'public.json'}], 'preparation': True}, tmp_path/'proof', 'admitted_entry_call')
    if reported == 'prepared':
        modules['runner'].refuse(job, tmp_path/'negative', 5, completed=0, classes={'verification'})
    else:
        with pytest.raises(modules['io'].MeasurementError, match='refusal ingress differs'):
            modules['runner'].refuse(job, tmp_path/'negative', 5, completed=0, classes={'verification'})
