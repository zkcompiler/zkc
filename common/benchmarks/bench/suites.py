"""Protocol adapters: source preparation, comparison contracts and independent gates."""
from dataclasses import replace
import json
from pathlib import Path
import shutil

from .io import Journal, ROOT, digest, require, write_json
from .runner import CONTROL, Job, execute_job, refuse
from .projects import freeze_project
from .workloads import Protocol, catalog as protocol_catalog
from .coverage import catalog as execution_catalog, SMOKE


def catalog():
    return protocol_catalog() + execution_catalog()


class ProofChecks:
    """Check output identity across controls, CLI calls and every worker process."""
    def __init__(self, randomized):
        self.randomized = randomized
        self.seen = set()

    def observe(self, proof):
        value = digest(proof)
        if self.randomized:
            require(value not in self.seen, 'randomized prover repeated a proof')
        elif self.seen:
            require(value in self.seen, 'deterministic proof bytes differ')
        self.seen.add(value)


def prepare(args, output, capture, manifest):
    selected = [c for c in catalog() if (not args.case or c[0] in args.case)
                and (not args.suite or c[1].name in args.suite)]
    if args.preset == 'smoke':
        selected = [c for c in selected if c[0] in SMOKE]
    elif args.preset == 'execution':
        selected = [c for c in selected if not isinstance(c[1], Protocol)]
    elif args.preset == 'stark':
        selected = [c for c in selected if c[1].name in ('air', 'stark', 'fri', 'polynomial', 'extension', 'transcript', 'machine')]
    require(selected, 'selection contains no cases')
    if args.execution_counts:
        require(all(not isinstance(c[1], Protocol) for c in selected), 'execution counts require source workloads')
    controls = [c for c in selected if not isinstance(c[1], Protocol)]
    selected = [c for c in selected if isinstance(c[1], Protocol)]
    suites = {c[1].name: c[1] for c in selected}
    journal = capture_sources(args, output, capture, manifest, suites)
    packages = compile_projects(args, output, capture, manifest, suites, journal)
    all_jobs, by_case, proof_checks = [], {}, {}
    for name, protocol, size in selected:
        jobs, gate = prepare_case(args, output, capture, manifest, name, protocol, size, packages[protocol.name])
        all_jobs.extend(jobs)
        by_case[name], proof_checks[name] = jobs, gate

    execution_checks = {}
    from .execution import prepare_case as prepare_execution
    for name, case, _ in controls:
        jobs, gate = prepare_execution(args, output, capture, manifest, case)
        all_jobs.extend(jobs)
        execution_checks[name] = gate

    def check(job, proof, directory, input_index):
        if job.case in execution_checks:
            return execution_checks[job.case](job, proof, directory, input_index)
        if job.operation == 'prove':
            proof_checks[job.case].observe(proof)
            # The other implementation validates the exact timed output bytes.
            other = next(j for j in by_case[job.case] if j.operation == 'verify' and j.implementation != job.implementation)
            execute_job(replace(other, proof=proof), directory, CONTROL, args.timeout)
    return all_jobs, check


def capture_sources(args, output, capture, manifest, suites):
    root = args.source.resolve()
    journal = Journal(output / 'preparation', args.timeout)
    for name in ('compiler', 'runtime', 'worker'):
        capture.add(getattr(args, name))
    # The executing harness and worker sources are evidence, not proof of a binary build.
    for path in sorted((ROOT / 'common/benchmarks').rglob('*')):
        if path.is_file() and path.suffix in ('.py', '.cpp'):
            capture.add(path, Path('measurement') / path.relative_to(ROOT))
    for path in sorted((root / 'crates/zkc-benchmarks').rglob('*')):
        if path.is_file() and path.suffix in ('.rs', '.toml'):
            capture.add(path, Path('source') / path.relative_to(root))
    for name in ('Cargo.toml', 'Cargo.lock', 'flake.lock', 'uv.lock', 'rust-toolchain.toml'):
        capture.add(root / name, Path('source') / name)
    for name in ('scripts/processes.py', 'common/tests/support/project.py'):
        capture.add(ROOT / name, Path('measurement') / name)
    def git(tree, *argv):
        record = journal.command(['git', '-C', tree, *argv], cwd=tree)
        return Path(record['stdout']).read_text().strip()
    for name, tree in (('source', root), ('harness', ROOT)):
        manifest[name] = {'revision': git(tree, 'rev-parse', 'HEAD'), 'status': git(tree, 'status', '--short')}
    for protocol in suites.values():
        tool = getattr(args, protocol.reference_tool)
        require(tool is not None, f'{protocol.name} requires --{protocol.reference_tool}')
        capture.add(tool)
        if protocol.environment is not None:
            protocol.environment(args, root, capture, journal, manifest)
    return journal


def compile_projects(args, output, capture, manifest, suites, journal):
    root = args.source.resolve()
    packages = {}
    manifest['compilation'] = {}
    for suite in sorted(suites):
        project = freeze_project(root, suites[suite].project, capture)
        directory = output / 'packages' / suite
        directory.mkdir(parents=True)
        package = directory / 'proof.zkpkg'
        records = []
        for i in range(args.processes):
            target = directory / f'{i}.zkpkg'
            record = journal.command([args.runtime, '--json', 'compile', f'--compiler={args.compiler}',
                                      f'--project={project}', 'example::Proof', f'--output={target}'], cwd=root)
            report = json.loads(Path(record['stdout']).read_text())
            require(report.get('status') == 'compiled', 'compilation did not publish a package')
            require(digest(target) == report['package_sha256'], 'published package identity mismatch')
            records.append({'wall_seconds': record['wall_seconds'], 'sha256': digest(target),
                            'bytes': target.stat().st_size, 'report': report})
            if i == 0: shutil.copyfile(target, package)
            require(digest(target) == digest(package), 'compilation changed package bytes between repetitions')
        capture.add(package)
        packages[suite] = package
        manifest['compilation'][suite] = records
    return packages


def prepare_case(args, output, capture, manifest, name, protocol, size, package):
    root = args.source.resolve()
    suite = protocol.name
    directory = output / 'cases' / name
    directory.mkdir(parents=True)
    public, witness, changed = protocol.inputs(root, size, capture)
    for filename, content in [('public.json', public), ('witness.json', witness), ('changed.json', changed)]:
        write_json(directory / filename, content)
        capture.add(directory / filename)
    public_path, witness_path = directory / 'public.json', directory / 'witness.json'
    host = {'kind': 'host', 'package': str(package), 'sha256': digest(package),
            'inputs': [{'public': str(public_path), 'witness': str(witness_path)}], 'preparation': True}
    reference = {'kind': suite, 'public': str(public_path)}
    if protocol.witness: reference['witness'] = str(witness_path)
    implementations = [('zkc', args.worker, host, 'admitted_entry_call'),
                       ('reference', getattr(args, protocol.reference_tool),
                        reference, 'reference_proof_call')]
    manifest['contracts'][name] = {'protocol': suite, 'size': size, 'field': protocol.field,
        'transcript': protocol.transcript, 'encoding': protocol.encoding, 'public_sha256': digest(public_path),
        'witness_sha256': digest(witness_path), 'threads': args.threads,
        'input_policy': 'repeated fixed statement; fresh internal prover randomness where used',
        'comparison': 'complete implementation stacks; input validation and primitive implementations may differ',
        'verification': protocol.verification, 'randomized_prover': protocol.randomized,
        'notes': protocol.notes,
        'boundaries': {impl: boundary for impl, _, _, boundary in implementations},
        'included': ['transcript initialization', 'statement binding', 'proof encoding or decoding',
                     'protocol arithmetic', 'protocol temporaries'],
        'zkc_additions': ['input admission and adaptation', 'interpreter', 'service lifecycle', 'named output reconstruction'],
        'excluded': ['package admission', 'input JSON decoding', 'request construction',
                     'proof file I/O', 'independent output validation']}
    manifest.setdefault('comparisons', []).extend(
        {'case': name, 'operation': operation, 'numerator': 'zkc', 'denominator': 'reference'}
        for operation in ('prove', 'verify'))
    jobs = []
    for impl, executable, backend, boundary in implementations:
        proof = directory / f'{impl}.proof'
        job = Job(name, impl, 'prove', executable, backend, proof, boundary)
        control = execute_job(job, directory / f'{impl}-produce', CONTROL, args.timeout)
        shutil.copyfile(control['proof']['path'], proof)
        capture.add(proof)
        jobs += [job, replace(job, operation='verify')]
    # Cross verification and negative controls precede any performance run.
    for job in (j for j in jobs if j.operation == 'verify'):
        for other in (j for j in jobs if j.operation == 'prove'):
            execute_job(replace(job, proof=other.proof), directory / f'{job.implementation}-accept-{other.implementation}', CONTROL, args.timeout)
        proof = job.proof.read_bytes()
        for mutation, value in [('truncated', proof[:-1]), ('trailing', proof+b'\x00')]:
            bad = directory / f'{job.implementation}-{mutation}.proof'
            bad.write_bytes(value)
            refuse(replace(job, proof=bad), directory / f'{job.implementation}-{mutation}',
                   args.timeout, truncated=mutation == 'truncated')
        changed_backend = (job.backend | {'inputs': [job.backend['inputs'][0] | {'public': str(directory / 'changed.json')}]}) if job.implementation == 'zkc' else job.backend | {'public': str(directory / 'changed.json')}
        refuse(replace(job, backend=changed_backend),
               directory / f'{job.implementation}-changed', args.timeout)
    # CLI execution is retained as a different, separately named boundary.
    cli = Journal(directory / 'cli', args.timeout)
    flags = [f'--package={package}', f'--sha256={digest(package)}', f'--public={public_path}', '--allow-authored']
    cli_proof = directory / 'cli.proof'
    produced = cli.command([args.runtime, '--json', 'prove', *flags, f'--witness={witness_path}', f'--output={cli_proof}'], cwd=root)
    verified = cli.report([args.runtime, '--json', 'verify', *flags, f'--proof={cli_proof}'], cwd=root, status='accepted')[1]
    manifest.setdefault('cli', {})[name] = {'prove_wall_seconds': produced['wall_seconds'], 'verify_wall_seconds': verified['wall_seconds']}
    capture.add(cli_proof)
    gate = ProofChecks(protocol.randomized)
    controls = [j.proof for j in jobs if j.operation == 'prove'] + [cli_proof]
    for proof in controls:
        gate.observe(proof)
    manifest['checks'].append({'case': name, 'status': 'passed', 'directory': str(directory),
                               'cross_verification': 'both directions',
                               'rejections': ['changed-statement', 'truncated', 'trailing'],
                               'proofs': [capture.files[str(path.resolve())] for path in controls]})
    # Both timed verifiers consume the same reference-produced bytes.
    reference_proof = next(j.proof for j in jobs if j.implementation == 'reference')
    jobs = [replace(j, proof=reference_proof) if j.operation == 'verify' else j for j in jobs]
    return jobs, gate
