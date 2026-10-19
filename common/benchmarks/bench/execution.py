"""Adapt generated source workloads to the existing benchmark scheduler."""
from dataclasses import replace
import hashlib
import json
from pathlib import Path

from .io import Journal, digest, require, write_json
from .runner import CONTROL, Job, execute_job, refuse
from .projects import project_inputs


def compile_program(args, output, capture, manifest, case, program):
    root = args.source.resolve()
    directory = output/'cases'/case.identifier
    directory.mkdir(parents=True, exist_ok=True)
    source = directory/'main.zkc'
    source.write_text(program.source)
    project = directory/'zkc.toml'
    text = f'format="zkc.project/0"\n[modules]\n{json.dumps(program.entry.split("::")[0])}="main.zkc"\n[dependencies]\n'
    text += ''.join(f'{json.dumps(name)}={{workspace={json.dumps(name)}}}\n' for name in program.dependencies)
    if program.dependencies:
        text += f'\n[workspace]\npath={json.dumps(str(root/"zkc.workspace.toml"))}\n'
    for name, value in program.assets.items():
        path = directory/f'{name}.json'
        write_json(path, value)
        text += f'\n[assets.{name}]\nformat="relation-bundle-json"\npath={json.dumps(str(path))}\n'
    project.write_text(text)
    manifests = []
    modules, assets = project_inputs(project, manifests=manifests)
    paths = {*manifests, *modules.values(), *(p for _, p in assets.values()), *program.support}
    copied = {}
    for path in sorted(paths):
        require(path.is_relative_to(root) or path.is_relative_to(directory), 'generated input is outside the captured roots')
        relative = (Path('source')/path.relative_to(root) if path.is_relative_to(root)
                    else Path('generated')/case.identifier/path.relative_to(directory))
        capture.add(path, relative)
        copied[path] = capture.directory/relative
    flags = [f'--module={name}={copied[path]}' for name, path in sorted(modules.items())]
    flags += [f'--asset={name}={kind}={copied[path]}' for name, (kind, path) in sorted(assets.items())]
    package = directory/'entry.zkpkg'
    record = Journal(directory/'compile', args.timeout).command(
        [args.compiler, 'language-package', '--source-format=zkc', f'--entry={program.entry}',
         *args.compiler_option, *flags],
        cwd=root, stdout=package)
    capture.add(package)
    manifest.setdefault('compilation', {})[case.identifier] = [{'wall_seconds': record['wall_seconds'],
                                                               'sha256': digest(package), 'bytes': package.stat().st_size}]
    return directory, package


def prepare_case(args, output, capture, manifest, case):
    print(f'prepare {case.identifier}', flush=True)
    program = case.generate(args.source.resolve(), output/'cases'/case.identifier, timeout=args.timeout)
    directory, package = compile_program(args, output, capture, manifest, case, program)
    proof_format = (json.loads(json.loads(package.read_text())['interface'])['job']['construction']['format']
                    if program.proof else None)
    inputs = list(program.inputs)
    if program.proof:
        for index in range(1, args.input_count):
            other = case.generate(args.source.resolve(), directory, index, timeout=args.timeout)
            require(other.source == program.source and other.assets == program.assets, 'changing input changed the program')
            inputs.extend(other.inputs)
        require(args.input_count == 1 or (args.iterations == 1 and args.samples % args.input_count == 0
                and args.warmups % args.input_count == 0), 'changing inputs require complete sample/warmup cycles with --iterations 1')
        if args.input_count > 1:
            require(len({json.dumps(pair['public'], sort_keys=True) for pair in inputs}) == len(inputs), 'changing public statements were not distinct')
    files = []
    identities = []
    for index, entry in enumerate(inputs):
        row, hashes = {}, {}
        for name, values in entry.items():
            path = directory/f'{index}-{name}.json'
            write_json(path, values)
            capture.add(path)
            row[name], hashes[name] = str(path), digest(path)
        files.append(row)
        identities.append(hashes)
    manifest['contracts'][case.identifier] = {
        'protocol': case.name, 'category': case.category, 'dimensions': case.shape, 'proof_format': proof_format,
        'operation_mix': case.mix, 'oracle': program.oracle, 'inputs': identities,
        'source_sha256': hashlib.sha256(program.source.encode()).hexdigest(),
        'assets_sha256': hashlib.sha256(json.dumps(program.assets, sort_keys=True).encode()).hexdigest(),
        'input_policy': 'round-robin distinct inputs' if len(inputs) > 1 else 'fixed inputs',
        'preparation_policy': args.preparation if program.proof else 'run entry defaults',
        'requested_preparation_entries': args.preparation_entries if program.proof else None,
        'requested_preparation_bytes': args.preparation_bytes if program.proof else None,
        'notes': [case.limitation, 'SDK timing includes result checking in the source; excludes input JSON decoding, final diagnostics and proof-file writes.',
                  'Generated-project compilation is a single compiler-process observation, excluding source generation.'],
        'boundaries': {},
    }
    boundary = 'admitted_entry_call' if program.proof else 'admitted_run_call'
    base = {'package': str(package), 'sha256': digest(package)}
    if not program.proof:
        backend = base | {'kind': 'run', 'roles': files[0], 'accept_role': 'P'}
        job = Job(case.identifier, 'zkc', 'run', args.worker, backend, directory/'unused', boundary, execution_counts=args.execution_counts)
        execute_job(job, directory/'control', CONTROL, args.timeout)
        # The generator supplies a typed incorrect expectation for its own domain.
        require(program.incorrect is not None, 'run workload needs an incorrect-result control')
        bad_roles = {}
        for role, values in program.incorrect.items():
            path = directory/f'incorrect-{role}.json'
            write_json(path, values)
            capture.add(path)
            bad_roles[role] = str(path)
        request = directory/'incorrect-request.json'
        write_json(request, {'format': 'zkc.benchmark-job/0', 'operation': 'run', 'plan': CONTROL,
            'backend': backend | {'roles': bad_roles}, 'proof': str(directory/'unused')})
        record = Journal(directory/'incorrect', args.timeout).command([args.worker, request], cwd=directory, expected=None)
        report = json.loads(Path(record['stdout']).read_text())
        require(record['returncode'] > 0 and report.get('status') == 'incorrect-result',
                'incorrect result did not fail at the acceptance gate')
        jobs = [job]
        def check(*unused):
            return None
    else:
        jobs, check = proof_jobs(args, capture, directory, case.identifier, base, files, program, proof_format)
    contract = manifest['contracts'][case.identifier]
    contract['boundaries'] = {j.implementation: j.boundary for j in jobs}
    manifest['checks'].append({'case': case.identifier, 'status': 'passed', 'directory': str(directory),
                               'oracle': program.oracle, 'proof_validation': 'same stack, every timed output' if program.proof else None})
    if program.proof and args.preparation == 'both':
        manifest.setdefault('comparisons', []).extend({'case': case.identifier, 'operation': op,
            'numerator': 'unprepared', 'denominator': 'zkc'} for op in ('prove', 'verify'))
    return jobs, check


def proof_jobs(args, capture, directory, name, base, files, program, proof_format):
    require(proof_format in ('raw.bytes/0', 'zkc.framed/0'), 'unknown proof format for refusal controls')
    backend = base | {'kind': 'host', 'inputs': files, 'preparation': True, 'preparation_entries': args.preparation_entries,
                      'preparation_bytes': args.preparation_bytes}
    prototype = Job(name, 'zkc', 'prove', args.worker, backend, directory/'proof.bin', 'admitted_entry_call', execution_counts=args.execution_counts)
    # Generate a candidate for every statement, outside the measurement schedule.
    for index, inputs in enumerate(files):
        job = replace(prototype, backend=backend | {'inputs': [inputs]})
        result = execute_job(job, directory/f'produce-{index}', CONTROL, args.timeout)
        inputs['proof'] = result['proof']['path']
        capture.add(Path(inputs['proof']))
    # These mutations exercise format, statement binding, and the mathematical
    # verifier separately. Every warm refusal follows one successful invocation.
    first = files[0]
    mutations = []
    for label, data in [('truncated', Path(first['proof']).read_bytes()[:-1]),
                        ('trailing', Path(first['proof']).read_bytes()+b'\x00')]:
        path = directory/f'{label}.proof'
        path.write_bytes(data)
        capture.add(path)
        mutations.append((label, first | {'proof': str(path)}, label == 'truncated'))
    if program.changed is not None:
        path = directory/'changed.json'
        write_json(path, program.changed)
        capture.add(path)
        mutations.append(('changed', first | {'public': str(path)}, False))
    if len(files) > 1:
        mutations.append(('swapped', files[1] | {'proof': first['proof']}, False))
    if program.invalid_witness is not None:
        path = directory/'invalid-witness.json'
        write_json(path, program.invalid_witness)
        capture.add(path)
        invalid = first | {'witness': str(path)}
        result = execute_job(replace(prototype, backend=backend | {'inputs': [invalid]}),
                             directory/'produce-invalid', CONTROL, args.timeout)
        path = Path(result['proof']['path'])
    elif program.mutate_proof is not None:
        path = directory/'invalid-response.proof'
        path.write_bytes(program.mutate_proof(Path(first['proof']).read_bytes()))
    else:
        raise ValueError('proof workload needs a semantic negative control')
    capture.add(path)
    mutations.append(('semantic', first | {'proof': str(path)}, False))
    jobs = []
    policies = [('zkc', True), ('unprepared', False)] if args.preparation == 'both' else [
        ('zkc' if args.preparation == 'enabled' else 'unprepared', args.preparation == 'enabled')]
    for implementation, enabled in policies:
        candidate = replace(prototype, implementation=implementation, backend=backend | {'preparation': enabled}, proof=Path(first['proof']))
        jobs.extend([candidate, replace(candidate, operation='verify')])
        verifier = replace(candidate, operation='verify', backend=candidate.backend | {'inputs': [first]})
        execute_job(verifier, directory/f'{implementation}-accept', CONTROL, args.timeout)
        for label, invalid, truncated in mutations:
            for warm in (False, True):
                inputs = [first, invalid] if warm else [invalid]
                refuse(replace(verifier, backend=verifier.backend | {'inputs': inputs}, proof=Path(invalid['proof'])),
                       directory/f'{implementation}-{label}-{"warm" if warm else "cold"}', args.timeout,
                       truncated=truncated, completed=1 if warm else 0,
                       classes={'verification'} if label == 'semantic' else
                               {'binding', 'verification'} if label in ('changed', 'swapped') else {'verification'} if proof_format == 'raw.bytes/0' else {'format'})

    def check(job, proof, target, input_index):
        require(type(input_index) is int and 0 <= input_index < len(files), 'invalid proof input identity')
        verifier = replace(job, operation='verify', proof=proof,
                           backend=job.backend | {'inputs': [files[input_index] | {'proof': str(proof)}]})
        execute_job(verifier, target, CONTROL, args.timeout)
    return jobs, check
