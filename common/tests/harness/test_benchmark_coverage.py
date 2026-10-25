"""Mathematical oracles and evidence integrity, without performance thresholds."""
import importlib
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

import pytest


@pytest.fixture
def modules(monkeypatch, tmp_path):
    root = Path(__file__).resolve().parents[3]
    monkeypatch.syspath_prepend(str(root/'common/benchmarks'))
    loaded = {name: importlib.import_module(f'bench.{name}') for name in
              ('algebra', 'coverage', 'programs', 'stark', 'io', 'runner', 'results')}
    monkeypatch.setattr(loaded['io'], 'MEASUREMENT_LOCK', tmp_path/'measurement.lock')
    return loaded


def host_backend():
    return {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64,
            'ingress': 'json', 'inputs': [{'public': 'public.json'}], 'preparation': True}


def negative_report(completed=0):
    return {'format': 'zkc.benchmark-worker/0', 'ingress': 'json', 'status': 'rejected',
            'error': 'proof rejected', 'completed_calls': completed, 'refusal': None,
            'preparation': None if completed is None else {
                phase: {'entries': 0, 'retained_bytes': 0, 'hits': 0} for phase in ('before', 'after')},
            'preparation_limits': None if completed is None else lifecycle_worker()['lifecycle']['preparation_limits']}


@pytest.mark.parametrize('size', [1, 2, 8, 32])
@pytest.mark.parametrize('degree', [1, 8])
def test_coset_oracle_matches_horner_at_every_point(modules, size, degree):
    a = modules['algebra']
    coefficients = a.dense(size, degree, 131)
    shift = a.dense(1, degree, 132)[0]
    root = pow(1791270792, (1 << 24)//size, a.P)
    expected = [a.horner(coefficients, tuple(x*pow(root, i, a.P) % a.P for x in shift)) for i in range(size)]
    assert a.coset(coefficients, shift, size) == expected


def test_coverage_has_matched_forms_and_independent_stark_dimensions(modules):
    cases = modules['coverage'].cases()
    names = {c.identifier for c in cases}
    assert len(names) == len(cases)
    assert set(modules['coverage'].SMOKE) <= names
    assert {c.name for c in cases} >= {'finite', 'matrix', 'curve', 'pairing', 'control', 'transcript', 'air', 'stark', 'fri', 'machine'}
    for field in ('koala-bear', 'bls12-381.fr'):
        for n in (0, 17, 1024, 8192):
            forms = [c for c in cases if c.name == 'finite' and c.shape['field'] == field and c.shape['elements'] == n]
            assert {c.shape['form'] for c in forms} == {'reduce', 'collect', 'bulk', 'total-collect-fold', 'total-fold'}
            programs = [modules['programs'].finite(c.shape) for c in forms]
            assert all(program.inputs == programs[0].inputs for program in programs)
    air = [c.shape for c in cases if c.name == 'air']
    assert len({s['height'] for s in air if s['width'] == 1}) >= 3
    assert all(any(s['height'] >= 1024 and s['width'] == width for s in air) for width in (1, 4))
    assert len({s['width'] for s in air if s['height'] == 32 and s['evaluation_size'] == 128}) >= 3
    assert len({s['evaluation_size'] for s in air if s['height'] == 32 and s['width'] == 4}) >= 2
    # Original KoalaBear library controls retain exactly the air cases' shapes.
    assert sorted(map(str, air)) == sorted(str(c.shape) for c in cases
                                         if c.name == 'stark' and 'field' not in c.shape)


def test_generated_compilation_forwards_explicit_policy(modules, tmp_path):
    execution = importlib.import_module('bench.execution')
    root = tmp_path / 'source'
    root.mkdir()
    output = tmp_path / 'output'
    output.mkdir()
    compiler = tmp_path / 'compiler'
    arguments = tmp_path / 'arguments.json'
    compiler.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
Path({str(arguments)!r}).write_text(json.dumps(sys.argv[1:]))
for a in sys.argv[1:]:
    if a.startswith('--observations='): Path(a.split('=',1)[1]).write_text(json.dumps({{'completed':True}}))
print('{{"options":{{}}}}')
''')
    compiler.chmod(0o755)
    args = SimpleNamespace(source=root, compiler=compiler, timeout=5,
                           compiler_option=['--fuse-collect-fold', '--no-finite-bulk'])
    case = next(c for c in modules['coverage'].cases() if c.identifier == 'finite-kb-total-collect-fold-17')
    program = modules['programs'].Program('module example;', [], dependencies=())
    manifest = {}
    capture = modules['runner'].Capture(output / 'capture')
    _, package = execution.compile_program(args, output, capture, manifest, case, program)
    forwarded = json.loads(arguments.read_text())
    assert all(forwarded.count(option) == 1 for option in args.compiler_option)
    assert forwarded[0] == 'language-package'
    assert manifest['compilation'][case.identifier][0]['sha256'] == modules['io'].digest(package)


def test_numerical_forms_share_inputs_and_empty_reduction_identities(modules):
    generate = modules['programs'].numerical
    for field in ('koala-bear', 'bls12-381.fr', 'koala-bear.ext8-binomial3'):
        for size in (0, 17):
            for sink in ('map', 'sum', 'product'):
                programs = [generate({'field': field, 'elements': size, 'sink': sink, 'form': form})
                            for form in ('map', 'collect', 'bulk')]
                assert all(p.inputs == programs[0].inputs for p in programs)
                value = programs[0].inputs[0]['P']
                assert programs[0].incorrect != programs[0].inputs[0]
                if field.endswith('ext8-binomial3'):
                    assert all(int(x) != 0 for x in value['c'][1:])
                if size == 0:
                    expected = [] if sink == 'map' else ('0' if sink == 'sum' else '1')
                    if sink != 'map' and field.endswith('ext8-binomial3'):
                        expected = [expected] + ['0'] * 7
                    assert value['expected'] == expected


def test_generated_families_capture_workspace_dependency_closures(modules, tmp_path):
    execution = importlib.import_module('bench.execution')
    root = Path(__file__).resolve().parents[3]
    compiler = tmp_path/'compiler'
    compiler.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
for a in sys.argv[1:]:
    if a.startswith('--observations='): Path(a.split('=',1)[1]).write_text(json.dumps({{'completed':True}}))
print('{{"options":{{}}}}')
''')
    compiler.chmod(0o755)
    args = SimpleNamespace(source=root, compiler=compiler, timeout=10, compiler_option=[])
    families = {}
    for case in modules['coverage'].cases():
        families.setdefault(case.name, case)
    capture = modules['runner'].Capture(tmp_path/'capture')
    for family, case in families.items():
        directory = tmp_path/'generated'/family
        directory.mkdir(parents=True)
        program = case.generate(root, directory)
        execution.compile_program(args, tmp_path/'output', capture, {}, case, program)
    assert (capture.directory/'source/zkc.workspace.toml').is_file()
    assert (capture.directory/'source/libraries/core/primitives/algebra/curve.zkc').is_file()
    assert (capture.directory/'source/libraries/arguments/stark/whole_bundle/zkc.toml').is_file()
    capture.check()


def test_distinct_stark_statements_keep_the_same_program(modules, tmp_path):
    root = Path(__file__).resolve().parents[3]
    for family in ('fri', 'air', 'stark', 'transcript', 'bulletproofs'):
        case = next(c for c in modules['coverage'].cases() if c.name == family)
        programs = [case.generate(root, tmp_path, i) for i in range(4)]
        left, right = programs[:2]
        assert left.source == right.source and left.assets == right.assets
        assert left.inputs[0]['public'] != right.inputs[0]['public']
        assert all(program.changed not in [other.inputs[0]['public'] for other in programs]
                   for program in programs)


def test_shared_slot_is_exclusive_fail_fast_and_preserves_evidence(modules, tmp_path):
    io = modules['io']
    output = tmp_path/'new'
    with io.measurement_slot(output/'coordination.json', exclusive=True):
        output.mkdir()
        code = ('import fcntl,sys; f=open(sys.argv[1],"a"); '
                'fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)')
        other = subprocess.run([sys.executable, '-c', code, io.MEASUREMENT_LOCK], capture_output=True)
        assert other.returncode > 0 and b'BlockingIOError' in other.stderr
        with pytest.raises(io.MeasurementBusy):
            with io.measurement_slot(tmp_path/'other/coordination.json', exclusive=True):
                pytest.fail('nested slot acquired')
    evidence = output/'coordination.json'
    original = evidence.read_bytes()
    record = json.loads(original)
    assert record['attempted_utc'] <= record['acquired_utc'] <= record['finished_utc']
    with pytest.raises(FileExistsError):
        with io.measurement_slot(evidence, exclusive=True):
            pytest.fail('existing evidence accepted')
    assert evidence.read_bytes() == original
    assert io.MEASUREMENT_LOCK.exists()


def test_command_inherits_the_owned_lock_descriptor(modules, tmp_path):
    io = modules['io']
    with io.measurement_slot(tmp_path/'run/coordination.json', exclusive=True):
        fd = io._measurement_fd.get()
        script = 'import os,sys; assert os.fstat(int(sys.argv[1])).st_ino == os.stat(sys.argv[2]).st_ino'
        io.Journal(tmp_path/'run/commands', 10).command(
            [sys.executable, '-c', script, str(fd), io.MEASUREMENT_LOCK], cwd=tmp_path)


def test_command_intervals_survive_failure(modules, tmp_path):
    io = modules['io']
    journal = io.Journal(tmp_path/'commands', 10)
    with pytest.raises(io.MeasurementError):
        journal.command([sys.executable, '-c', 'raise SystemExit(7)'], cwd=tmp_path)
    record = json.loads((tmp_path/'commands/commands.jsonl').read_text())
    assert record['returncode'] == 7
    assert record['started_utc'] <= record['finished_utc']


def lifecycle_worker(times=(10, 100, 30, 300)):
    calls = [{'input_index': i % 2, 'decode_ns': 5, 'request_ns': 2, 'preparation': {'entries': 0, 'retained_bytes': 0, 'hits': 0}} for i in range(4)]
    return {'format': 'zkc.benchmark-worker/0', 'status': 'passed', 'boundary': 'admitted_entry_call',
        'proof_bytes': 4, 'admission_ns': 3, 'process_peak_rss_bytes': 100, 'proofs': [],
        'build': {'optimized': True, 'debug_assertions': False, 'execution_counts': False}, 'process': {'rayon_num_threads': '1', 'cpu_workers': 1}, 'timer_floor_ns': 1,
        'diagnostics': {}, 'lifecycle': {'ingress': 'json', 'input_setup': [], 'preparation_limits': {'entries':128, 'bytes':8388608, 'default_entries':128, 'default_bytes':8388608}, 'capture_ns': 1, 'admit_ns': 2, 'diagnostics_ns': 7,
            'peak_rss_before_diagnostics': 80, 'peak_rss_after_diagnostics': 100, 'calls': calls},
        'samples': [{'phase': 'warmup' if i < 2 else 'sample', 'index': i, 'iterations': 1,
                     'elapsed_ns': t, 'cpu_ns': t, 'first_call_ns': t} for i, t in enumerate(times)]}


@pytest.mark.parametrize('fault', ['missing', 'calls', 'admission', 'decode', 'identity', 'stats'])
def test_lifecycle_evidence_is_checked(modules, fault):
    worker = lifecycle_worker()
    if fault == 'missing': worker['lifecycle'] = None
    elif fault == 'calls': worker['lifecycle']['calls'].pop()
    elif fault == 'admission': worker['admission_ns'] = 99
    elif fault == 'decode': worker['lifecycle']['calls'][0]['decode_ns'] = -1
    elif fault == 'identity': worker['lifecycle']['calls'][0]['input_index'] = True
    else: worker['lifecycle']['calls'][0]['preparation'] = {'entries': -1}
    with pytest.raises(modules['io'].MeasurementError):
        modules['results'].validate_worker(worker, {'warmups': 2, 'samples': 2, 'iterations': 1}, 'admitted_entry_call')


@pytest.mark.parametrize('fault,diagnostic', [
    ('entries', 'preparation exceeded its resource contract'),
    ('bytes', 'preparation exceeded its resource contract'),
    ('hits', 'preparation hits moved backwards'),
    ('zero_entries', 'disabled preparation retained state'),
    ('zero_bytes', 'disabled preparation retained state'),
])
def test_saved_worker_preparation_must_respect_its_contract(modules, fault, diagnostic):
    worker = lifecycle_worker()
    limits = worker['lifecycle']['preparation_limits']
    stats = worker['lifecycle']['calls'][0]['preparation']
    if fault == 'entries': stats['entries'] = limits['entries'] + 1
    elif fault == 'bytes': stats['retained_bytes'] = limits['bytes'] + 1
    elif fault == 'hits': stats['hits'] = 1  # The next call cannot have fewer hits.
    else:
        limits[fault.removeprefix('zero_')] = 0
        for call in worker['lifecycle']['calls']:
            call['preparation']['hits'] = 1
    with pytest.raises(modules['io'].MeasurementError, match=diagnostic):
        modules['results'].validate_worker(worker, {'warmups': 2, 'samples': 2, 'iterations': 1}, 'admitted_entry_call')


@pytest.mark.parametrize('entries,capacity,accepted', [
    (512, 64 << 20, True), (128, 8 << 20, False),
    (512, 8 << 20, False), (128, 64 << 20, False),
])
def test_selected_limits_allow_retention_above_native_defaults(modules, entries, capacity, accepted):
    worker = lifecycle_worker()
    worker['lifecycle']['preparation_limits'].update(entries=entries, bytes=capacity)
    for call in worker['lifecycle']['calls']:
        call['preparation'].update(entries=200, retained_bytes=9 << 20)
    plan = {'warmups': 2, 'samples': 2, 'iterations': 1}
    if accepted:
        modules['results'].validate_worker(worker, plan, 'admitted_entry_call')
    else:
        with pytest.raises(modules['io'].MeasurementError, match='preparation exceeded its resource contract'):
            modules['results'].validate_worker(worker, plan, 'admitted_entry_call')


@pytest.mark.parametrize('entries,capacity,enabled', [
    (None, None, True), (512, None, True), (None, 64 << 20, True),
    (512, 64 << 20, True), (0, 0, True), (0, None, True), (None, 0, True), (512, 64 << 20, False),
])
@pytest.mark.parametrize('changed_bound', [None, 'entries', 'bytes'])
def test_worker_must_honor_both_requested_preparation_bounds(modules, tmp_path, entries, capacity, enabled, changed_bound):
    response = lifecycle_worker()
    limits = response['lifecycle']['preparation_limits']
    limits['entries'] = (limits['default_entries'] if entries is None else entries) if enabled else 0
    limits['bytes'] = (limits['default_bytes'] if capacity is None else capacity) if enabled else 0
    if changed_bound:
        limits[changed_bound] += 1
    executable = tmp_path/'worker'
    executable.write_text(f'#!{sys.executable}\nimport json\nprint(json.dumps({response!r}))\n')
    executable.chmod(0o755)
    backend = {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': enabled,
               'preparation_entries': entries, 'preparation_bytes': capacity}
    job = modules['runner'].Job('case', 'zkc', 'verify', executable, backend,
                               tmp_path/'proof', 'admitted_entry_call')
    plan = {'warmups': 2, 'samples': 2, 'iterations': 1}
    if changed_bound:
        with pytest.raises(modules['io'].MeasurementError, match='preparation limits differ'):
            modules['runner'].execute_job(job, tmp_path/'run', plan, 5)
    else:
        modules['runner'].execute_job(job, tmp_path/'run', plan, 5)


def test_changing_statements_keep_individual_first_visits_and_distributions(modules):
    job = {'case': 'case', 'implementation': 'zkc', 'operation': 'verify', 'boundary': 'admitted_entry_call',
           'backend': {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': True}}
    manifest = {'format': 'zkc.benchmark/0', 'ingress': 'json', 'compiler_options': [], 'observation': 'timing', 'status': 'passed', 'processes': 2,
                'threads': 1, 'host': {'requested_cpus': None, 'affinity': None},
                'plan': {'warmups': 2, 'samples': 2, 'iterations': 1}, 'matrix': [job],
                'results': [job | {'status': 'passed', 'repetition': i, 'worker': lifecycle_worker(times)}
                            for i, times in enumerate(((10, 100, 30, 300), (20, 200, 50, 500)))]}
    row = modules['results'].summarize(manifest)[0]
    assert [v['first_visit_ns']['median'] for v in row['inputs']] == [15, 150]
    assert [v['ns_per_call']['median'] for v in row['inputs']] == [40, 400]
    assert row['decode_ns_per_call']['median'] == 5


@pytest.mark.parametrize('backend', [
    {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': True, 'preparation_entries': 512},
    {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': True, 'preparation_bytes': 64 << 20},
    {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': False},
    None, 'absent',
])
def test_saved_manifest_checks_requested_limits(modules, backend):
    job = {'case': 'case', 'implementation': 'zkc', 'operation': 'verify',
           'boundary': 'admitted_entry_call'}
    if backend != 'absent':
        job['backend'] = backend
    manifest = {'format': 'zkc.benchmark/0', 'ingress': 'json', 'status': 'passed', 'processes': 1,
                'threads': 1, 'host': {'requested_cpus': None, 'affinity': None},
                'compiler_options': [], 'observation': 'timing',
                'plan': {'warmups': 2, 'samples': 2, 'iterations': 1}, 'matrix': [job],
                'results': [job | {'status': 'passed', 'repetition': 0, 'worker': lifecycle_worker()}]}
    with pytest.raises(modules['io'].MeasurementError, match='preparation (limits differ|request)'):
        modules['results'].validate_manifest(manifest)


def test_workers_receive_only_declared_environment(modules, monkeypatch):
    monkeypatch.setenv('ZKC_UNRECORDED_EXPERIMENT', '1')
    monkeypatch.setenv('PYTHONPATH', '/unrecorded')
    monkeypatch.setenv('UNRELATED_API_TOKEN', 'secret')
    monkeypatch.setenv('RAYON_NUM_THREADS', '3')
    environment = modules['io'].command_environment()
    assert not {'ZKC_UNRECORDED_EXPERIMENT', 'PYTHONPATH', 'UNRELATED_API_TOKEN'} & environment.keys()
    assert environment['RAYON_NUM_THREADS'] == '3'
    assert environment['LC_ALL'] == 'C'


@pytest.mark.parametrize('completed', [None, 0, 1, 2])
def test_warm_refusal_requires_a_successful_preceding_call(modules, tmp_path, completed):
    executable = tmp_path/'worker'
    response = negative_report(completed=completed)
    executable.write_text(f'#!{sys.executable}\nimport json,sys\nprint(json.dumps({response!r}))\nsys.exit(1)\n')
    executable.chmod(0o755)
    job = modules['runner'].Job('case', 'zkc', 'verify', executable, host_backend(), tmp_path/'proof', 'admitted_entry_call')
    if completed == 1:
        modules['runner'].refuse(job, tmp_path/'negative', 5, completed=1)
    else:
        with pytest.raises(modules['io'].MeasurementError, match='intended invocation'):
            modules['runner'].refuse(job, tmp_path/'negative', 5, completed=1)


@pytest.mark.parametrize('fault', [None, 'before_entries', 'after_bytes', 'hits', 'zero_entries', 'zero_bytes', 'request'])
def test_refusal_preparation_respects_requested_contract(modules, tmp_path, fault):
    limits = {'entries': 512, 'bytes': 64 << 20, 'default_entries': 128, 'default_bytes': 8 << 20}
    stats = {phase: {'entries': 200, 'retained_bytes': 9 << 20, 'hits': 1} for phase in ('before', 'after')}
    backend = {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'public.json'}], 'preparation': True, 'preparation_entries': 512, 'preparation_bytes': 64 << 20}
    if fault == 'before_entries': stats['before']['entries'] = 513
    elif fault == 'after_bytes': stats['after']['retained_bytes'] = (64 << 20) + 1
    elif fault == 'hits': stats['after']['hits'] = 0
    elif fault in ('zero_entries', 'zero_bytes'):
        bound = fault.removeprefix('zero_')
        limits[bound] = backend[f'preparation_{bound}'] = 0
        for observation in stats.values(): observation.update(entries=0, retained_bytes=0)
    elif fault == 'request': limits['entries'] = 256
    response = {'format': 'zkc.benchmark-worker/0', 'ingress': 'json', 'status': 'rejected', 'completed_calls': 1,
                'preparation': stats, 'preparation_limits': limits, 'error': 'proof rejected', 'refusal': None}
    executable = tmp_path/'worker'
    executable.write_text(f'#!{sys.executable}\nimport json,sys\nprint(json.dumps({response!r}))\nsys.exit(1)\n')
    executable.chmod(0o755)
    job = modules['runner'].Job('case', 'zkc', 'verify', executable, backend, tmp_path/'proof', 'admitted_entry_call')
    if fault is None:
        modules['runner'].refuse(job, tmp_path/'negative', 5, completed=1)
    else:
        with pytest.raises(modules['io'].MeasurementError, match='preparation'):
            modules['runner'].refuse(job, tmp_path/'negative', 5, completed=1)


def test_every_run_has_a_generator_owned_incorrect_expectation(modules):
    root = Path(__file__).resolve().parents[3]
    for case in modules['coverage'].cases():
        if case.name in ('fri', 'air', 'stark', 'bulletproofs', 'machine', 'transcript'):
            continue
        program = case.generate(root, root/'unused')
        assert program.incorrect is not None
        assert program.incorrect != program.inputs[0]
        assert program.incorrect.keys() == program.inputs[0].keys()


def test_stark_claim_mutation_preserves_framing_and_canonical_coordinates(modules):
    a, stark = modules['algebra'], modules['stark']
    root = b'ZKCV\x00\x21' + bytes(32)
    claim = b'ZKCV\x00\x1b' + (1).to_bytes(4, 'little') + (a.P-1).to_bytes(4, 'little') + bytes(28)
    proof = b'ZKCPRF00' + bytes(32) + len(root).to_bytes(8, 'little') + root + len(claim).to_bytes(8, 'little') + claim
    mutated = stark.mutate_claim(proof)
    assert len(mutated) == len(proof)
    assert mutated[:-32] == proof[:-32]
    assert mutated[-32:] == bytes(32)
    with pytest.raises(ValueError, match='missing extension'):
        stark.mutate_claim(proof[:40])
    quartic = b'ZKCV\x00\x16' + (1).to_bytes(4, 'little') + (a.P-1).to_bytes(4, 'little') + bytes(12)
    proof = b'ZKCPRF00' + bytes(32) + len(quartic).to_bytes(8, 'little') + quartic
    mutated = stark.mutate_claim(proof, b'ZKCV\x00\x16', 26)
    assert len(mutated) == len(proof) and mutated[-16:] == bytes(16)
    with pytest.raises(ValueError, match='missing extension'):
        stark.mutate_claim(proof)


@pytest.mark.parametrize('observed', ['format', 'binding', 'verification', None])
def test_semantic_control_cannot_pass_at_the_format_layer(modules, tmp_path, observed):
    executable = tmp_path/'worker'
    response = negative_report()
    response['refusal'] = {'class': observed, 'code': None, 'stop': None} if observed else None
    executable.write_text(f'#!{sys.executable}\nimport json,sys\nprint(json.dumps({response!r}))\nsys.exit(1)\n')
    executable.chmod(0o755)
    job = modules['runner'].Job('case', 'zkc', 'verify', executable, host_backend(), tmp_path/'proof', 'admitted_entry_call')
    if observed == 'verification':
        modules['runner'].refuse(job, tmp_path/'negative', 5, classes={'verification'})
    else:
        with pytest.raises(modules['io'].MeasurementError, match='wrong layer'):
            modules['runner'].refuse(job, tmp_path/'negative', 5, classes={'verification'})


def test_fri_invalid_word_is_not_a_single_position_perturbation(modules, tmp_path):
    root = Path(__file__).resolve().parents[3]
    case = next(c for c in modules['coverage'].cases() if c.name == 'fri')
    program = case.generate(root, tmp_path)
    valid = program.inputs[0]['witness']['word']
    invalid = program.invalid_witness['word']
    assert len(invalid) == len(valid)
    assert all(x != y for x, y in zip(valid, invalid, strict=True))


def test_monero_response_control_refuses_framed_or_noncanonical_layout(modules):
    mutate = modules['coverage'].library_cases.mutate_response
    raw = bytes(160)
    changed = mutate(raw)
    assert len(changed) == len(raw) and changed[:96] == raw[:96]
    assert int.from_bytes(changed[96:128], 'little') == 1
    for invalid in (b'ZKCPRF00'+bytes(152), bytes(96)+b'\xff'*32):
        with pytest.raises(ValueError, match='raw Monero'):
            mutate(invalid)


@pytest.mark.parametrize('bound', ['entries', 'bytes', 'default_entries', 'default_bytes'])
def test_comparison_rejects_changed_preparation_bounds(modules, bound):
    from copy import deepcopy
    job = {'case': 'case', 'implementation': 'zkc', 'operation': 'verify', 'boundary': 'admitted_entry_call',
           'backend': {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': True}}
    baseline = {'format': 'zkc.benchmark/0', 'ingress': 'json', 'compiler_options': [], 'observation': 'timing', 'status': 'passed', 'processes': 1,
                'plan': {'warmups': 2, 'samples': 2, 'iterations': 1}, 'matrix': [job], 'host': {'requested_cpus': None, 'affinity': None}, 'threads': 1, 'contracts': {},
                'results': [job | {'status': 'passed', 'repetition': 0, 'worker': lifecycle_worker()}]}
    changed = deepcopy(baseline)
    changed['results'][0]['worker']['lifecycle']['preparation_limits'][bound] *= 2
    name = bound.removeprefix('default_')
    changed['matrix'][0]['backend'][f'preparation_{name}'] = changed['results'][0]['worker']['lifecycle']['preparation_limits'][name]
    with pytest.raises(modules['io'].MeasurementError, match='preparation limits differ'):
        modules['results'].compare(baseline, changed)


def test_air_declares_its_generator_dependency(modules, tmp_path):
    root = Path(__file__).resolve().parents[3]
    case = next(c for c in modules['coverage'].cases() if c.name == 'air')
    assert root/'compiler/adapters/ring_arena.py' in case.generate(root, tmp_path).support


def test_termination_during_python_preparation_retains_failure_evidence(modules, tmp_path):
    root = Path(__file__).resolve().parents[3]
    output = tmp_path/'interrupted'
    script = f"""
import os, signal, sys
from pathlib import Path
from types import SimpleNamespace
sys.path.insert(0, {str(root/'common/benchmarks')!r})
from bench import io, runner
io.MEASUREMENT_LOCK = Path({str(tmp_path/'slot')!r})
args = SimpleNamespace(output=Path({str(output)!r}), exclusive=True, samples=1, warmups=0, iterations=1,
    processes=1, seed=0, cpus=None, threads=1, label='signal', timeout=1, ingress='json', execution_counts=False, compiler_option=[])
def prepare(*args):
    os.kill(os.getpid(), signal.SIGTERM)
raise SystemExit(runner.run(args, prepare))
"""
    result = subprocess.run([sys.executable, '-c', script], capture_output=True, timeout=10)
    assert result.returncode == 1, result.stderr
    assert json.loads((output/'manifest.json').read_text())['status'] == 'interrupted'
    assert json.loads((output/'coordination.json').read_text())['finished_utc']


def test_crashed_refusal_reports_the_command_logs(modules, tmp_path):
    io = modules['io']
    with pytest.raises(io.MeasurementError, match='invalid command report; see .*stderr'):
        io.Journal(tmp_path/'commands', 10).report(
            [sys.executable, '-c', 'raise SystemExit(101)'], cwd=tmp_path,
            status='rejected', refused=True)


def counted_manifest():
    from bench.observations import EVENTS
    worker = lifecycle_worker()
    worker['build']['execution_counts'] = True
    for call in worker['lifecycle']['calls']:
        call['execution_counts'] = {'events': dict.fromkeys(EVENTS, 0), 'operations': {}}
    job = {'case': 'case', 'implementation': 'zkc', 'operation': 'verify', 'boundary': 'admitted_entry_call',
           'backend': {'kind': 'host', 'package': 'entry.zkpkg', 'sha256': '0'*64, 'ingress': 'json', 'inputs': [{'public': 'first.json'}, {'public': 'second.json'}], 'preparation': True}}
    return {'format': 'zkc.benchmark/0', 'ingress': 'json', 'compiler_options': [], 'observation': 'execution_counts', 'status': 'passed',
            'threads': 1, 'host': {'requested_cpus': None, 'affinity': None},
            'processes': 1, 'plan': {'warmups': 2, 'samples': 2, 'iterations': 1},
            'matrix': [job], 'contracts': {},
            'results': [job | {'status': 'passed', 'repetition': 0, 'worker': worker}]}


@pytest.mark.parametrize('fault', ['capability', 'missing', 'negative', 'boolean', 'event', 'histogram', 'frames'])
def test_execution_count_evidence_refuses_inconsistent_observations(modules, fault):
    manifest = counted_manifest()
    worker = manifest['results'][0]['worker']
    counts = worker['lifecycle']['calls'][0]['execution_counts']
    if fault == 'capability': worker['build']['execution_counts'] = False
    elif fault == 'missing': del worker['lifecycle']['calls'][0]['execution_counts']
    elif fault == 'negative': counts['events']['local_op'] = -1
    elif fault == 'boolean': counts['events']['local_op'] = True
    elif fault == 'event': counts['events']['unrecognized'] = 0
    elif fault == 'histogram': counts['operations']['field.add'] = 1
    else: counts['events']['backend_enter_calls'] = 1
    with pytest.raises(modules['io'].MeasurementError):
        modules['results'].validate_manifest(manifest)


def test_execution_counts_publish_no_timing_comparisons(modules, tmp_path):
    manifest = counted_manifest()
    modules['results'].publish(tmp_path, manifest)
    summary = json.loads((tmp_path/'summary.json').read_text())
    row = summary['rows'][0]
    assert 'ns_per_call' not in row
    assert 'first_call_ns' not in row
    assert row['counts_repeatable'] is None
    assert summary['comparisons'] == []
    assert len(row['execution_counts']) == 4
    assert [(r['input_index'], r['first_visit']) for r in row['execution_counts']] == [(0, True), (1, True), (0, False), (1, False)]
    assert 'timing comparisons are intentionally omitted' in (tmp_path/'report.md').read_text()
    with pytest.raises(modules['io'].MeasurementError, match='refuses instrumented'):
        modules['results'].compare(manifest, manifest)
    manifest['observation'] = 'timing'
    with pytest.raises(modules['io'].MeasurementError, match='capability mismatch'):
        modules['results'].validate_manifest(manifest)


def test_count_sequences_expose_process_variation_without_losing_order(modules):
    from copy import deepcopy
    manifest = counted_manifest()
    manifest['processes'] = 2
    other = deepcopy(manifest['results'][0])
    other['repetition'] = 1
    manifest['results'].append(other)
    assert modules['results'].summarize(manifest)[0]['counts_repeatable']
    other['worker']['lifecycle']['calls'][2]['execution_counts']['events']['retention_plan_calls'] = 1
    row = modules['results'].summarize(manifest)[0]
    assert not row['counts_repeatable']
    assert len(row['execution_counts']) == 8



def test_failed_count_report_keeps_run_and_cell_errors(modules, tmp_path):
    manifest = counted_manifest()
    manifest['status'] = 'failed'
    manifest['error'] = 'measurement interrupted'
    manifest['results'][0].update(status='failed', error='worker refused input')
    modules['results'].publish(tmp_path, manifest)
    text = (tmp_path/'report.md').read_text()
    assert 'measurement interrupted' in text
    assert 'worker refused input' in text
    assert 'No comparison is published' in text
    assert json.loads((tmp_path/'summary.json').read_text())['comparisons'] == []


def test_exploratory_run_does_not_create_a_lock_and_records_failure(modules, tmp_path):
    io = modules['io']
    output = tmp_path/'exploratory'
    with pytest.raises(RuntimeError, match='worker failed'):
        with io.measurement_slot(output/'coordination.json'):
            output.mkdir()
            assert io._measurement_fd.get() is None
            raise RuntimeError('worker failed')
    assert not io.MEASUREMENT_LOCK.exists()
    record = json.loads((output/'coordination.json').read_text())
    assert record['mode'] == 'uncoordinated'
    assert record['path'] is None and record['acquired_utc'] is None
    assert record['attempted_utc'] <= record['started_utc'] <= record['finished_utc']
    with pytest.raises(FileExistsError):
        with io.measurement_slot(output/'coordination.json'):
            pytest.fail('existing results accepted')


def test_exploratory_run_proceeds_while_another_process_holds_the_slot(modules, tmp_path):
    io = modules['io']
    code = ('import fcntl,sys; f=open(sys.argv[1],"a"); '
            'fcntl.flock(f,fcntl.LOCK_EX); print("locked",flush=True); sys.stdin.read()')
    holder = subprocess.Popen([sys.executable, '-c', code, io.MEASUREMENT_LOCK],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    try:
        assert holder.stdout.readline().strip() == 'locked'
        output = tmp_path/'parallel'
        with io.measurement_slot(output/'coordination.json'):
            output.mkdir()
            assert io._measurement_fd.get() is None
        with pytest.raises(io.MeasurementBusy):
            with io.measurement_slot(tmp_path/'exclusive/coordination.json', exclusive=True):
                pytest.fail('exclusive acquisition accepted')
    finally:
        holder.communicate(timeout=10)
    assert holder.returncode == 0
