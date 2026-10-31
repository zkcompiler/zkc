"""Placement is a checked experimental condition, not a provider thread budget."""
import importlib
import pytest


@pytest.fixture
def env(monkeypatch):
    from pathlib import Path
    monkeypatch.syspath_prepend(str(Path(__file__).resolve().parents[3]/'common/benchmarks'))
    return importlib.import_module('bench.environment')


@pytest.mark.parametrize('text,expected', [('2', [2]), ('2,4-6', [2,4,5,6]), ('4,2-4', [2,3,4]), ('0-0', [0])])
def test_cpu_lists_are_canonical(env, text, expected):
    assert env.cpu_list(text) == expected


def test_cli_requires_the_current_cpu_option_spelling(env, monkeypatch, tmp_path):
    import sys
    from harness import load
    cli = load('benchmark_cpu_cli', 'common/benchmarks/run.py')
    selections = []
    monkeypatch.setattr(cli, 'run', lambda args, _: selections.append(args.cpus) or 0)
    arguments = ['run', '--compiler', sys.executable, '--runtime', sys.executable,
                 '--worker', sys.executable, '--output', str(tmp_path/'run')]
    assert cli.main([*arguments, '--cpus', '2-3']) == 0
    assert selections == [[2, 3]]
    with pytest.raises(SystemExit) as error:
        cli.main([*arguments, '--cpu', '2'])
    assert error.value.code == 2


@pytest.mark.parametrize('text', ['', '2,,3', '-1', '4-2', '1-', '1,', '1.0', '9999999999', '0-9999999999', None])
def test_cpu_lists_refuse_invalid_ranges(env, text):
    with pytest.raises(ValueError): env.cpu_list(text)


def test_every_surviving_thread_must_stay_inside_selected_set(env):
    from bench.io import MeasurementError
    host = {'requested_cpus': [2,4,5], 'affinity': [2,4,5]}
    process = {'affinity': '2,4-5', 'rayon_num_threads': '2', 'cpu_workers': 2,
               'thread_observation_errors': [],
               'thread_affinities': [{'tid': 12, 'cpus': '2,4-5'}, {'tid': 13, 'cpus': '4-5'}]}
    env.validate_process(process, host, 2, {'kind': 'host'})
    process['thread_observation_errors'] = ['permission denied']
    with pytest.raises(MeasurementError, match='incomplete'): env.validate_process(process, host, 2, {'kind': 'host'})
    process['thread_observation_errors'] = []
    process['thread_affinities'][1]['cpus'] = '0-5'
    with pytest.raises(MeasurementError, match='escaped'): env.validate_process(process, host, 2, {'kind': 'host'})
    process['thread_affinities'] = []
    with pytest.raises(MeasurementError, match='missing'): env.validate_process(process, host, 2, {'kind': 'host'})


def test_runtime_isa_is_the_intersection_of_selected_cpus(env):
    text = 'processor : 0\nflags : sse avx\n\nprocessor : 2\nflags : sse aes\n'
    assert env.cpu_features(text, [0]) == ['avx', 'sse']
    assert env.cpu_features(text, [0, 2]) == ['sse']
    assert env.cpu_features(text, [0, 1]) == []
    assert env.cpu_features('', [0]) == []
    assert env.cpu_features('processor: 3\nFeatures: asimd aes\n', [3]) == ['aes', 'asimd']


def test_affinity_is_restored_when_preparation_fails(env, monkeypatch, tmp_path):
    import os
    from types import SimpleNamespace
    from bench import runner
    selections = []
    monkeypatch.setattr(os, 'sched_getaffinity', lambda _: {2,4,5})
    monkeypatch.setattr(os, 'sched_setaffinity', lambda _, cpus: selections.append(cpus))
    args = SimpleNamespace(output=tmp_path/'run', cpus=[2,4], threads=2, exclusive=False,
        samples=1, warmups=0, iterations=1, processes=1, seed=0, label='test',
        compiler_option=[], ingress='json', execution_counts=False)
    def prepare(*_): raise ValueError('preparation deliberately refused')
    assert runner.run(args, prepare) == 1
    assert selections == [{2,4}, {2,4,5}]
    args.output, args.cpus = tmp_path/'outside', [1]
    selections.clear()
    assert runner.run(args, prepare) == 1
    assert selections == [{2,4,5}]


def test_saved_success_rechecks_worker_placement(env):
    from copy import deepcopy
    import json
    from pathlib import Path
    from bench.results import validate_manifest
    from bench.io import MeasurementError
    fixtures = json.loads((Path(__file__).parent/'fixtures/benchmark-evidence.json').read_text())
    document = deepcopy(fixtures['reference'])
    document['threads'] = 2
    document['host']['requested_cpus'] = [2,4]
    document['host']['affinity'] = [2,4]
    for row in document['results']:
        row['worker']['process'] = {'affinity':'2,4', 'rayon_num_threads':'2', 'cpu_workers':2,
                                    'thread_observation_errors': [],
                                    'thread_affinities':[{'tid':1,'cpus':'2,4'}]}
    validate_manifest(document)
    document['results'][0]['worker']['process']['thread_affinities'][0]['cpus'] = '0-4'
    with pytest.raises(MeasurementError, match='escaped'): validate_manifest(document)


@pytest.mark.parametrize('removed', ['threads', 'requested_cpus', 'affinity'])
def test_saved_measurements_require_their_placement_policy(env, removed):
    from copy import deepcopy
    import json
    from pathlib import Path
    from bench.io import MeasurementError
    from bench.results import validate_manifest
    document = deepcopy(json.loads((Path(__file__).parent/'fixtures/benchmark-evidence.json').read_text())['reference'])
    del (document if removed == 'threads' else document['host'])[removed]
    with pytest.raises(MeasurementError): validate_manifest(document)


@pytest.mark.parametrize('workers', [4, 1, None, True])
def test_cli_observations_request_and_check_workers(env, tmp_path, workers):
    import sys
    from types import SimpleNamespace
    from bench.io import MeasurementError
    from bench.suites import observe_cli

    runtime = tmp_path/'runtime'
    cpu = {'workers': workers} if workers is not None else {}
    runtime.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
assert '--threads=4' in sys.argv
operation=sys.argv[2]
if operation == 'prove':
    Path(next(v.split('=',1)[1] for v in sys.argv if v.startswith('--output='))).write_bytes(b'proof')
cpu={cpu!r}
print(json.dumps({{'status':'produced' if operation == 'prove' else 'accepted','cpu':cpu}}))
''')
    runtime.chmod(0o755)
    package = tmp_path/'proof.zkpkg'
    package.write_bytes(b'package')
    args = SimpleNamespace(runtime=runtime, source=tmp_path, timeout=5, threads=4)
    if type(workers) is int and workers == 4:
        proof, observations = observe_cli(args, tmp_path, package, 'public.json', 'witness.json')
        assert proof.read_bytes() == b'proof'
        assert observations['workers'] == 4
        assert all(observations[f'{operation}_wall_seconds'] > 0 for operation in ('prove', 'verify'))
    else:
        with pytest.raises(MeasurementError, match='CLI worker count'):
            observe_cli(args, tmp_path, package, 'public.json', 'witness.json')


@pytest.mark.parametrize('fault', ['workers', 'missing_workers', 'boolean_workers', 'nan', 'negative', 'extra'])
def test_saved_cli_observations_recheck_policy_and_times(env, fault):
    from copy import deepcopy
    import json
    from pathlib import Path
    from bench.io import MeasurementError
    from bench.results import validate_manifest

    document = deepcopy(json.loads((Path(__file__).parent/'fixtures/benchmark-evidence.json').read_text())['reference'])
    value = {'workers': document['threads'], 'prove_wall_seconds': 0.1, 'verify_wall_seconds': 0.2}
    document['cli'] = {'case': value}
    validate_manifest(document)
    if fault == 'workers': value['workers'] += 1
    elif fault == 'missing_workers': del value['workers']
    elif fault == 'boolean_workers': value['workers'] = True
    elif fault == 'extra': value['extra'] = 1
    else: value['prove_wall_seconds'] = float('nan') if fault == 'nan' else -1
    with pytest.raises(MeasurementError): validate_manifest(document)


@pytest.mark.parametrize('status', ['failed', 'interrupted', 'running'])
@pytest.mark.parametrize('threads', [0, -1, 257, True, 1.0, None])
def test_incomplete_cli_observations_require_a_valid_thread_request(env, status, threads):
    from copy import deepcopy
    import json
    from pathlib import Path
    from bench.io import MeasurementError
    from bench.results import validate_manifest

    document = deepcopy(json.loads((Path(__file__).parent/'fixtures/benchmark-evidence.json').read_text())['reference'])
    document.update(status=status, matrix=[], results=[])
    observation = {'workers': 256, 'prove_wall_seconds': 0.1, 'verify_wall_seconds': 0.2}
    document.update(threads=256, cli={'case': observation})
    validate_manifest(document)
    document['threads'] = threads
    observation['workers'] = threads if type(threads) is int else 1
    with pytest.raises(MeasurementError, match='invalid CLI thread setting'):
        validate_manifest(document)


@pytest.mark.parametrize('kind', ['host', 'run', 'kernel', 'schnorr', 'sumcheck'])
@pytest.mark.parametrize('workers', [None, True, 0, 1, '2', 3])
def test_native_workers_require_the_observed_owner_count(env, kind, workers):
    from bench.io import MeasurementError
    process = {'rayon_num_threads': '2'}
    if workers is not None:
        process['cpu_workers'] = workers
    with pytest.raises(MeasurementError, match='shared CPU context'):
        env.validate_process(process, {'requested_cpus': None}, 2, {'kind': kind})
    process['cpu_workers'] = 2
    env.validate_process(process, {'requested_cpus': None}, 2, {'kind': kind})


@pytest.mark.parametrize('kind', ['monero', 'c_kzg'])
def test_foreign_workers_have_a_separate_thread_policy(env, kind):
    env.validate_process({'rayon_num_threads': '2'}, {'requested_cpus': None}, 2, {'kind': kind})


@pytest.mark.parametrize('fixture', ['ingress', 'reference'])
def test_saved_native_measurements_require_owner_evidence(env, fixture):
    from copy import deepcopy
    import json
    from pathlib import Path
    from bench.io import MeasurementError
    from bench.results import validate_manifest
    document = deepcopy(json.loads((Path(__file__).parent/'fixtures/benchmark-evidence.json').read_text())[fixture])
    # Reuse archived worker payloads solely as CPU-owner evidence. Their old
    # STARK envelope has no current oracle policy and cannot attest a deployment.
    for row in [*document['matrix'], *document['results']]:
        if row['case'].startswith('stark-'):
            row['case'] = 'worker-host-control'
    validate_manifest(document)
    del document['results'][0]['worker']['process']['cpu_workers']
    with pytest.raises(MeasurementError, match='shared CPU context'):
        validate_manifest(document)
