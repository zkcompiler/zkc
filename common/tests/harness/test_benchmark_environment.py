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
    process = {'affinity': '2,4-5', 'rayon_num_threads': '2',
               'thread_observation_errors': [],
               'thread_affinities': [{'tid': 12, 'cpus': '2,4-5'}, {'tid': 13, 'cpus': '4-5'}]}
    env.validate_process(process, host, 2)
    process['thread_observation_errors'] = ['permission denied']
    with pytest.raises(MeasurementError, match='incomplete'): env.validate_process(process, host, 2)
    process['thread_observation_errors'] = []
    process['thread_affinities'][1]['cpus'] = '0-5'
    with pytest.raises(MeasurementError, match='escaped'): env.validate_process(process, host, 2)
    process['thread_affinities'] = []
    with pytest.raises(MeasurementError, match='missing'): env.validate_process(process, host, 2)


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
        row['worker']['process'] = {'affinity':'2,4', 'rayon_num_threads':'2',
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
