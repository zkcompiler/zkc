"""Focused controls for the maintained measurement driver; no project builds."""

import json
from pathlib import Path
import subprocess
import shutil
import sys

import pytest

from harness import load


@pytest.fixture
def measurement():
    return load('protocol_measurements', 'common/benchmarks/protocol_math.py')


def test_complete_protocol_profiles_and_independent_fri_values(measurement):
    cases = measurement.case_catalog()
    assert len(cases) == 10 and len({c['name'] for c in cases}) == 10
    for size, rounds in [(32, 3), (64, 4)]:
        public, witness = measurement.fri_inputs(size, rounds)
        assert public['round_count'] == str(rounds)
        assert len(witness['word']) == size
        # At row zero x=3+u. Independently expand every (3+u)^k by the
        # binomial theorem and reduce u^8=3; this does not reuse Horner/mul.
        from math import comb
        polynomial = [0] * ((1 << rounds) + 8)
        for k in range(1 << rounds):
            for offset, coefficient in [(0, k + 1), (1, k * k), (7, 1)]:
                for power in range(k + 1):
                    polynomial[power + offset] += coefficient * comb(k, power) * 3 ** (k - power)
        expected = [0] * 8
        for power, coefficient in enumerate(polynomial):
            expected[power % 8] += coefficient * 3 ** (power // 8)
        assert list(map(int, witness['word'][0])) == [n % measurement.P for n in expected]
        assert witness['word'][0] != witness['word'][1]


def test_preparation_uses_maintained_scripts_and_records_profile_edits(measurement, tmp_path):
    journal = measurement.Journal(tmp_path / 'commands', 30)
    frozen = tmp_path / 'source'
    for source in measurement.source_files(measurement.ROOT, measurement.case_catalog()):
        target = frozen / source.relative_to(measurement.ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    for case in measurement.case_catalog():
        directory = tmp_path / case['name']
        flags = measurement.prepare_case(frozen, case, directory, journal)
        assert all(str(measurement.ROOT / 'common/tests') not in flag for flag in flags)
        public = json.loads((directory / 'public.json').read_text())
        if case['project'] == 'accumulator-machine':
            assert public['memory_present'] == case['memory_present']
            assert public['cpu_height'] == ('16' if case['memory_present'] else '4')
            if case['memory_present']:
                assert public['memory_height'] == '32'
        if case['name'] == 'air-stark-64':
            assert 'TableArgument<0,Recurrence,3,6,8,8>' in (directory / 'main.zkc').read_text()


def test_unknown_profile_anchor_refuses_instead_of_silent_wrong_shape(measurement, tmp_path):
    case = measurement.case_catalog()[0] | {'replacement': ['absent-anchor', 'replacement']}
    with pytest.raises(measurement.MeasurementError, match='anchor must occur once'):
        measurement.prepare_case(measurement.ROOT, case, tmp_path / 'case',
                                 measurement.Journal(tmp_path / 'commands', 5))


def test_raw_journal_preserves_nonzero_and_timeout(measurement, tmp_path):
    journal = measurement.Journal(tmp_path, .2)
    with pytest.raises(measurement.MeasurementError, match='exited 3'):
        journal.command([sys.executable, '-c', 'print("retained");raise SystemExit(3)'], cwd=tmp_path)
    with pytest.raises(subprocess.TimeoutExpired):
        journal.command([sys.executable, '-c', 'import time;print("partial",flush=True);time.sleep(5)'],
                        cwd=tmp_path)
    records = [json.loads(line) for line in (tmp_path / 'commands.jsonl').read_text().splitlines()]
    assert records[0]['returncode'] == 3
    assert 'retained' in Path(records[0]['stdout']).read_text()
    assert records[1]['returncode'] is None
    assert 'TimeoutExpired' in records[1]['error']
    assert 'partial' in Path(records[1]['stdout']).read_text()


def test_refusal_requires_nonzero_status_not_crash_or_success(measurement, tmp_path):
    journal = measurement.Journal(tmp_path, 5)
    for code, status in [(0, 'refused'), (1, 'accepted')]:
        with pytest.raises(measurement.MeasurementError, match='expected refused'):
            journal.report([sys.executable, '-c', f'print(\'{{"status":"{status}"}}\');exit({code})'],
                           cwd=tmp_path, status='refused', refused=True)


def test_missing_counters_are_not_zero_or_peak_memory(measurement):
    report = {'execution': {key: 7 for key in measurement.COUNTERS}}
    result = measurement.execution_metrics(report)
    assert result['total_value_bytes'] == 7
    assert all(value is None for value in result['exit_storage'].values())
    assert 'live_value_bytes' in result['exit_storage_unavailable']
    assert 'peak' not in json.dumps(result)
    del report['execution']['ring_work']
    with pytest.raises(measurement.MeasurementError, match='missing required'):
        measurement.execution_metrics(report)


def test_trace_keeps_nested_stages_and_declines_without_adding_times(measurement):
    trace = measurement.trace_summary('''remark: mathematical stage expand: completed, 9 -> 12 operations, 20 us
remark: mathematical decision 1 scope=2 parent=1 service=finite outcome=unsupported
remark: mathematical stage finish: completed, 12 -> 12 operations, 5 us
''')
    assert [s['microseconds'] for s in trace['stages']] == [20, 5]
    assert trace['aggregate_realization_work'] is None
    assert trace['decisions'] == ['1 scope=2 parent=1 service=finite outcome=unsupported']


def small_package():
    original = '''"builtin.module"() ({
  "protocol.module"() ({
    "local.binding"() <{contract = "vector.map", sym_name = "binding"}> : () -> ()
    %0 = "local.invoke"() : () -> i1
  }) : () -> ()
}) : () -> ()
'''
    program = ['zkc.program/0', [['binding', 'vector.map', ['field'], 'native/vector.map']],
               [['function', 'helper', [], [], [['op', 'site', 'binding', [], [], []]]]], [], []]
    return {'format': 'zkc.entry/0', 'original': original,
            'artifact': json.dumps(['zkc.native-proof/0', '', [], '', json.dumps(program), '', [], [], []]),
            'options': {'simplify': True, 'release_storage': False,
                        'finite_bulk': True, 'fuse_vector_reductions': False,
                        'calculation_batching': True}}


def test_inventory_counts_static_sites_and_bound_contracts(measurement):
    package = small_package()
    logical = measurement.logical_inventory(package['original'])
    assert logical['operations']['local.invoke'] == 1
    assert logical['binding_declarations'] == {'vector.map': 1}
    kernels = measurement.kernel_inventory(package)
    assert kernels['kernels'][0]['call_sites'] == 1
    assert kernels['kernels'][0]['implementation'] == 'native/vector.map'
    with pytest.raises(measurement.MeasurementError, match='generic protocol'):
        measurement.logical_inventory('module {}')


def test_failed_group_never_summarizes_partial_timings(measurement):
    result = measurement.summaries([{'case': 'fri-32', 'variant': 'baseline/default',
                                    'status': 'failed', 'compile_wall_seconds': .001}])
    assert result == [{'case': 'fri-32', 'variant': 'baseline/default', 'passed': 0, 'total': 1}]


def test_explicit_tools_and_positive_repetitions_are_required(measurement, tmp_path):
    base = ['--baseline-only', '--baseline-revision', 'expected', '--baseline-source', str(tmp_path), '--output', str(tmp_path / 'out')]
    for extra in [[], ['--repetitions', '0'], ['--baseline-runtime', 'nonexistent-tool']]:
        with pytest.raises(SystemExit) as error:
            measurement.parse_args(base + extra)
        assert error.value.code == 2


def test_trial_runs_controlled_tools_and_fails_closed(measurement, tmp_path):
    package = small_package()
    package_file = tmp_path / 'template.json'
    measurement.write_json(package_file, package)
    compiler = tmp_path / 'compiler'
    compiler.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
p=json.loads(Path({str(package_file)!r}).read_text())
print(p['original'] if sys.argv[1]=='language-emit' else json.dumps(p), end='')
''')
    compiler.chmod(0o755)
    runtime = tmp_path / 'runtime'
    runtime.write_text(f'''#!{sys.executable}
import hashlib,json,sys
from pathlib import Path
args=dict(x.split('=',1) for x in sys.argv if x.startswith('--') and '=' in x)
command=sys.argv[2]
if 'changed-public' in args.get('--public',''):
 print(json.dumps({{'status':'refused','phase':'execution','code':'artifact-binding'}}));exit(1)
if command=='prove': Path(args['--output']).write_bytes(b'proof')
print(json.dumps({{'status':'produced' if command=='prove' else 'accepted',
 'proof_sha256':hashlib.sha256(b'proof').hexdigest(),
 'execution':{{key:1 for key in {measurement.COUNTERS!r}}}}}))
''')
    runtime.chmod(0o755)
    inputs = tmp_path / 'inputs'
    measurement.write_json(inputs / 'public.json', {'query_count': '8'})
    measurement.write_json(inputs / 'witness.json', {})
    case = measurement.case_catalog()[0]
    measured = measurement.trial(case, 'baseline/default', [], inputs, tmp_path / 'run',
                                  (compiler, runtime, None), 5)
    assert measured['status'] == 'passed', measured
    assert measured['preparation']['available'] is False
    assert measured['package']['sha256'] == measurement.digest(tmp_path / 'run/entry.zkpkg')
    summary = measurement.summaries([measured, measured])[0]
    assert summary['passed'] == 2 and summary['metrics']['prove.instructions']['median'] == 1
    # Ignoring a requested compiler policy cannot produce an accepted sample.
    bad = measurement.trial(case, 'current/no-finite-bulk', [], inputs, tmp_path / 'bad',
                             (compiler, runtime, None), 5)
    assert bad['status'] == 'failed' and 'requested policy' in bad['error']
    assert (tmp_path / 'bad/result.json').is_file()


@pytest.mark.parametrize('failure', [None, 'revision', 'dirty'])
def test_baseline_snapshot_checks_revision_and_actual_bytes(measurement, tmp_path, monkeypatch, failure):
    root = tmp_path / 'root'
    root.mkdir()
    source = root / 'main.zkc'
    source.write_text('original' if failure != 'dirty' else 'dirty')
    monkeypatch.setattr(measurement, 'source_files', lambda root, cases: [source])

    class GitJournal:
        sequence = 0

        def command(self, args, **kwargs):
            self.sequence += 1
            out = tmp_path / f'git-{self.sequence}'
            if 'show' in args:
                content = 'original'
            elif 'status' in args:
                content = ''
            elif args[-1] == 'HEAD' and failure == 'revision':
                content = 'wrong'
            else:
                content = 'expected'
            out.write_text(content)
            return {'stdout': str(out)}

    if failure:
        with pytest.raises(measurement.MeasurementError, match='baseline'):
            measurement.snapshot(root, tmp_path / 'snapshot', [], GitJournal(), 'expected')
    else:
        record = measurement.snapshot(root, tmp_path / 'snapshot', [], GitJournal(), 'expected')
        assert record['files'] == {'main.zkc': measurement.digest(source)}


def test_existing_evidence_is_never_overwritten(measurement, tmp_path):
    args = ['--baseline-only', '--baseline-revision', 'expected', '--baseline-source', str(tmp_path),
            '--baseline-compiler', sys.executable, '--baseline-runtime', sys.executable,
            '--output', str(tmp_path)]
    marker = tmp_path / 'manifest.json'
    marker.write_text('previous run')
    assert measurement.main(args) == 2
    assert marker.read_text() == 'previous run'
