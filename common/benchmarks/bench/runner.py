"""Serial experiment lifecycle. Workloads supply prepared jobs and correctness gates."""
from collections import defaultdict
from dataclasses import dataclass
import json
import os
from pathlib import Path
import platform
import random
import shutil
import sys

from .io import Journal, digest, identity, measurement_slot, command_environment, performance_environment, read_report, require, write_json
from .results import FORMAT, publish, validate_manifest, validate_preparation, validate_worker

CONTROL = {'warmups': 0, 'samples': 1, 'iterations': 1}


@dataclass(frozen=True)
class Job:
    case: str
    implementation: str
    operation: str
    executable: Path
    backend: dict
    proof: Path
    boundary: str
    execution_counts: bool = False


class Capture:
    """Pin consumed files, retain small inputs, and detect concurrent replacement."""
    def __init__(self, directory):
        self.directory = directory
        self.files = {}

    def add(self, path, relative=None):
        path = Path(path).resolve()
        record = identity(path)
        if str(path) in self.files:
            require(record['sha256'] == self.files[str(path)]['sha256'], f'input changed during preparation: {path}')
        record['captures'] = self.files.get(str(path), {}).get('captures', [])
        if relative is not None:
            target = self.directory / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
            require(digest(target) == record['sha256'], f'input changed during capture: {path}')
            if str(target) not in record['captures']:
                record['captures'].append(str(target))
        self.files[str(path)] = record
        return record

    def check(self):
        for path, record in self.files.items():
            require(digest(Path(path)) == record['sha256'], f'input changed during run: {path}')
            for target in record['captures']:
                require(digest(Path(target)) == record['sha256'], f'captured input changed during run: {target}')


def host_info():
    cpuinfo = Path('/proc/cpuinfo')
    cpu = next((line.split(':', 1)[1].strip() for line in cpuinfo.read_text().splitlines()
                if line.startswith('model name')), None) if cpuinfo.is_file() else None
    affinity = sorted(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else None
    settings = [Path('/sys/devices/system/cpu') / path for path in
                ('smt/active', 'intel_pstate/no_turbo', 'cpufreq/boost')]
    settings += [Path(f'/sys/devices/system/cpu/cpu{i}/cpufreq/scaling_governor') for i in affinity or []]
    return {'platform': platform.platform(), 'machine': platform.machine(), 'python': sys.version,
            'cpu_model': cpu, 'cpu_count': os.cpu_count(),
            'affinity': affinity, 'command_environment': command_environment(), 'performance_environment': performance_environment(),
            'settings': {str(path): path.read_text().strip() for path in settings
                         if path.is_file()}}


def execute_job(job, directory, plan, timeout):
    directory.mkdir(parents=True)
    proof = directory / 'proof.bin' if job.operation == 'prove' else job.proof
    request = {'format': 'zkc.benchmark-job/0', 'backend': job.backend, 'operation': job.operation,
               'plan': plan, 'proof': str(proof)}
    path = directory / 'request.json'
    write_json(path, request)
    journal = Journal(directory / 'commands', timeout)
    command = journal.command([job.executable, path], cwd=directory)
    report = validate_worker(read_report(command), plan, job.boundary)
    require(report['build'].get('execution_counts', False) is job.execution_counts,
            'worker execution-counts feature differs from the requested observation')
    if job.backend.get('kind') in ('host', 'run'):
        count = len(job.backend['inputs']) if job.backend['kind'] == 'host' else 1
        require([c['input_index'] for c in report['lifecycle']['calls']] ==
                [i % count for i in range((plan['warmups']+plan['samples'])*plan['iterations'])],
                'worker changed the input schedule')
    if job.backend.get('kind') == 'host':
        previous_hits = 0
        limit = job.backend.get('preparation_entries')
        limits = report['lifecycle']['preparation_limits']
        limit = limits['default_entries'] if limit is None else limit
        expected = (limit, limits['default_bytes']) if job.backend['preparation'] else (0, 0)
        require((limits['entries'], limits['bytes']) == expected, 'preparation limits differ from the request')
        for call in report['lifecycle']['calls']:
            stats = call['preparation']
            require(stats['hits'] >= previous_hits, 'preparation hits moved backwards')
            previous_hits = stats['hits']
            require(stats['entries'] <= limits['entries'] and stats['retained_bytes'] <= limits['bytes'],
                    'preparation exceeded its resource contract')
            if not job.backend['preparation']:
                require(all(value == 0 for value in stats.values()), 'disabled preparation retained state')
    if job.operation == 'run':
        require(report['proof_bytes'] == 0, 'run worker reported a proof')
    elif job.operation == 'prove' or job.backend.get('kind') != 'host' or len(job.backend['inputs']) == 1:
        require(proof.is_file() and proof.stat().st_size == report['proof_bytes'], 'worker proof size mismatch')
    proofs = report.get('proofs', [])
    expected = (plan['warmups'] + plan['samples']) * plan['iterations'] if job.operation == 'prove' else 0
    require(len(proofs) == expected, 'worker did not retain every produced proof')
    paths = set()
    for index, artifact in enumerate(proofs):
        require(isinstance(artifact, dict) and isinstance(artifact.get('path'), str), 'invalid proof artifact')
        if job.backend.get('kind') == 'host':
            require(artifact.get('input_index') == index % len(job.backend['inputs']), 'proof input identity differs')
        path = Path(artifact['path']).resolve()
        require(path.parent == directory.resolve(), 'proof escaped worker directory')
        require(path not in paths, 'worker reused a proof artifact path')
        paths.add(path)
        require(type(artifact.get('bytes')) is int and artifact['bytes'] >= 0, 'missing proof size')
        require(path.is_file() and path.stat().st_size == artifact['bytes'], 'produced proof size differs')
        actual = identity(path)
        require(artifact.get('sha256') == actual['sha256'], 'produced proof digest differs')
        artifact.update(actual)
    return {'worker': report, 'process_wall_seconds': command['wall_seconds'],
            'proof': identity(proof) if proof.is_file() else None}


def run(args, prepare):
    # Acquisition is fail-fast and precedes compilation or worker launch.
    with measurement_slot(args.output.resolve() / 'coordination.json'):
        return run_locked(args, prepare)


def run_locked(args, prepare):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    original_affinity = None
    original_threads = os.environ.get('RAYON_NUM_THREADS')
    capture = Capture(output / 'capture')
    manifest = {'format': FORMAT, 'status': 'running', 'phase': 'preparation', 'results': [], 'contracts': {},
                'plan': {'samples': args.samples, 'warmups': args.warmups, 'iterations': args.iterations},
                'processes': args.processes, 'seed': args.seed, 'label': args.label,
                'observation': 'execution_counts' if args.execution_counts else 'timing',
                'argv': sys.argv, 'host': {}, 'files': capture.files, 'checks': []}
    try:
        if args.cpu is not None:
            require(hasattr(os, 'sched_setaffinity'), 'CPU affinity is unavailable')
            original_affinity = os.sched_getaffinity(0)
            require(args.cpu in original_affinity, 'CPU is outside current affinity')
            os.sched_setaffinity(0, {args.cpu})
        os.environ['RAYON_NUM_THREADS'] = str(args.threads)
        manifest['host'] = host_info()
        manifest['threads'] = args.threads
        jobs, check = prepare(args, output, capture, manifest)
        require(jobs, 'empty benchmark matrix')
        require(all(j.execution_counts == args.execution_counts for j in jobs), 'job observation mismatch')
        if args.execution_counts:
            require(all(j.backend.get('kind') in ('host', 'run') for j in jobs),
                    'execution counts require source workloads')
            require((args.warmups + args.samples)*args.iterations <= 128,
                    'execution counts permit at most 128 calls per worker')
        manifest['matrix'] = [{'case': j.case, 'implementation': j.implementation,
                               'operation': j.operation, 'boundary': j.boundary,
                               'executable': str(j.executable), 'backend': j.backend,
                               'proof': str(j.proof)} for j in jobs]
        rng = random.Random(args.seed)
        groups = defaultdict(list)
        for i, job in enumerate(jobs):
            groups[job.case, job.operation].append(i)
        for group in groups.values():
            rng.shuffle(group)
        manifest['schedule'] = []
        for repetition in range(args.processes):
            order = list(groups.values())
            rng.shuffle(order)
            manifest['schedule'].extend((repetition, i) for group in order
                                        for i in (group if repetition % 2 == 0 else reversed(group)))
        write_json(output / 'plan.json', {k: v for k, v in manifest.items() if k not in ('status', 'results')})
        publish(output, manifest)
        manifest['phase'] = 'measurement'
        measured = []
        for repetition, i in manifest['schedule']:
            job = jobs[i]
            directory = output / 'runs' / job.case / job.implementation / job.operation / str(repetition)
            result = {'case': job.case, 'implementation': job.implementation, 'operation': job.operation,
                      'repetition': repetition, 'status': 'failed'}
            manifest['results'].append(result)
            print(f'{job.case} {job.implementation} {job.operation} process {repetition+1}', flush=True)
            try:
                result.update(execute_job(job, directory, manifest['plan'], args.timeout))
                process = result['worker']['process']
                require(process.get('rayon_num_threads') == str(args.threads), 'worker thread setting differs')
                if args.cpu is not None:
                    affinity = process.get('affinity')
                    require(isinstance(affinity, str) and affinity.strip() == str(args.cpu), 'worker affinity differs')
                result['status'] = 'measured'
                measured.append((job, directory, result))
            except Exception as error:
                result['error'] = f'{type(error).__name__}: {error}'
            with (output/'progress.jsonl').open('a') as stream:
                stream.write(json.dumps(result) + '\n')
        publish(output, manifest)
        # Independent validation cannot perturb the order of timed worker pairs.
        manifest['phase'] = 'validation'
        for job, directory, result in measured:
            try:
                for index, proof in enumerate(result['worker']['proofs']):
                    require(digest(Path(proof['path'])) == proof['sha256'], 'produced proof changed before validation')
                    check(job, Path(proof['path']), directory / 'checks' / str(index), proof.get('input_index', 0))
                    require(digest(Path(proof['path'])) == proof['sha256'], 'produced proof changed during validation')
                result['validated_proofs'] = len(result['worker']['proofs'])
                result['status'] = 'passed'
            except Exception as error:
                result['status'] = 'failed'
                result['error'] = f'{type(error).__name__}: {error}'
        capture.check()
        manifest['status'] = 'passed' if all(r['status'] == 'passed' for r in manifest['results']) else 'failed'
        validate_manifest(manifest)
        manifest['phase'] = 'complete'
    except Exception as error:
        manifest['status'] = 'failed'
        manifest['error'] = f'{type(error).__name__}: {error}'
    except KeyboardInterrupt:
        manifest['status'] = 'interrupted'
    finally:
        if original_threads is None:
            os.environ.pop('RAYON_NUM_THREADS', None)
        else:
            os.environ['RAYON_NUM_THREADS'] = original_threads
        if original_affinity is not None:
            os.sched_setaffinity(0, original_affinity)
        publish(output, manifest)
    print(f"{manifest['status']}: {output / 'manifest.json'}", flush=True)
    return 0 if manifest['status'] == 'passed' else 1

def refuse(job, directory, timeout, *, truncated=False, completed=None, classes=None):
    directory.mkdir(parents=True)
    path = directory / 'request.json'
    write_json(path, {'format': 'zkc.benchmark-job/0', 'backend': job.backend, 'operation': 'verify',
                      'plan': CONTROL | {'samples': (completed or 0)+1}, 'proof': str(job.proof)})
    record = Journal(directory / 'commands', timeout).command([job.executable, path], cwd=directory, expected=None)
    require(record['returncode'] > 0, 'negative control was accepted or crashed')
    report = read_report(record)
    allowed = {'rejected', 'input-bounds'} if truncated else {'rejected'}
    require(isinstance(report, dict) and report.get('format') == 'zkc.benchmark-worker/0'
            and report.get('status') in allowed, 'negative control failed outside verification')

    if completed is not None:
        require(report.get('completed_calls') == completed, 'negative control failed before the intended invocation')
    if classes is not None and report['status'] == 'rejected':
        observed = report.get('refusal')
        require(isinstance(observed, dict) and observed.get('class') in classes,
                'negative control refused at the wrong layer')
    if job.backend.get('kind') == 'host' and completed is not None:
        stats = report.get('preparation')
        require(isinstance(stats, dict) and set(stats) == {'before', 'after'}, 'missing refusal preparation observations')
        for value in stats.values():
            validate_preparation(value)
            if not job.backend['preparation']:
                require(all(v == 0 for v in value.values()), 'disabled preparation retained state on refusal')
        require(stats['after']['hits'] >= stats['before']['hits'], 'refusal preparation hits moved backwards')
