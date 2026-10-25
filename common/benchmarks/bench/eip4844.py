"""Authored EIP-4844 operations against the pinned standalone c-kzg client."""
from dataclasses import dataclass, replace
import hashlib
import json
from pathlib import Path

from .execution import compile_program
from .io import Journal, digest, read_report, require, write_json
from .programs import Program
from .runner import CONTROL, Job, execute_job, refuse

MODULUS = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
SETUP_SHA256 = 'd39b9f2d047cc9dca2de58f264b6a09448ccd34db967881a6713eacacf0f26b7'


@dataclass(frozen=True)
class Case:
    identifier: str
    api: str
    count: int = 1
    name: str = 'eip4844'


def catalog():
    cases = [Case(f'eip4844-{api}', api) for api in ('commitment', 'opening', 'point', 'blob')]
    cases += [Case(f'eip4844-batch-{n}', 'batch', n) for n in (1, 4, 16)]
    return [(c.identifier, c, {'api': c.api, 'blobs': c.count, 'field_elements_per_blob': 4096}) for c in cases]


def blob(index):
    """Distinct, full-width canonical scalars, independent of either implementation."""
    return b''.join((int.from_bytes(hashlib.sha256(
        b'zkc eip4844 benchmark\x00' + index.to_bytes(4, 'big') + i.to_bytes(4, 'big')
    ).digest(), 'big') % MODULUS).to_bytes(32, 'big') for i in range(4096))


def frame(tag, payload, count=None):
    return b'ZKCV\x00' + bytes([tag]) + (len(payload) if count is None else count).to_bytes(4, 'little') + payload


def inputs(args, output, capture, manifest, count):
    directory = output/'inputs'/'eip4844'/str(count)
    result = directory/'expected.json'
    if result.is_file():
        return directory, json.loads(result.read_text())
    directory.mkdir(parents=True)
    setup = args.source.resolve()/'libraries/constructions/ethereum/eip4844/trusted_setup.txt'
    require(digest(setup) == SETUP_SHA256, 'EIP-4844 trusted setup differs from the pinned reference')
    capture.add(setup, 'inputs/eip4844/trusted_setup.txt')
    words = setup.read_text().split()
    require(words[:2] == ['4096', '65'], 'unexpected EIP-4844 trusted setup shape')
    (directory/'setup.zkcv').write_bytes(frame(67, b''.join(bytes.fromhex(w) for w in words[2:4098]), 4096))
    blobs = []
    for i in range(count):
        path = directory/f'blob-{i}.bin'
        path.write_bytes(blob(i))
        blobs.append(str(path))
    z = (int.from_bytes(hashlib.sha256(b'zkc point opening').digest(), 'big') % MODULUS).to_bytes(32, 'big')
    request = directory/'reference-inputs.json'
    write_json(request, {'blobs': blobs, 'commitments': [], 'z': z.hex()})
    Journal(directory/'reference-prepare', args.timeout).command(
        [args.c_kzg, '--prepare', request, setup], cwd=directory, stdout=result)
    expected = json.loads(result.read_text())
    require(len(expected['commitments']) == count and len(expected['proofs']) == count,
            'reference prepared an incorrect EIP-4844 input count')
    write_json(request, {'blobs': blobs, 'commitments': expected['commitments'], 'z': z.hex(), 'y': expected['y']})
    (directory/'blobs.zkcv').write_bytes(frame(70, b''.join(Path(p).read_bytes() for p in blobs)))
    (directory/'blob.zkcv').write_bytes(frame(70, Path(blobs[0]).read_bytes()))
    (directory/'blob.proof').write_bytes(b''.join(bytes.fromhex(p) for p in expected['proofs']))
    (directory/'point.proof').write_bytes(bytes.fromhex(expected['point_proof']))
    for path in sorted(directory.iterdir()):
        if path.is_file():
            capture.add(path)
    manifest.setdefault('references', {})['c_kzg'] = {
        'crate': 'c-kzg=2.1.8', 'revision': 'e125905e5e01186e6ccb7a0ced4845bf7eddbcfe',
        'setup_sha256': SETUP_SHA256, 'precompute': 0,
        'threading': 'ordinary EIP-4844 APIs are single-threaded',
    }
    return directory, expected


def prepare_case(args, output, capture, manifest, case):
    require(args.c_kzg is not None, 'EIP-4844 requires --c-kzg')
    require(not args.execution_counts, 'external EIP-4844 comparison requires an ordinary timing worker')
    require(args.input_count == 1, 'EIP-4844 uses its explicit blob-count dimension, not --input-count')
    capture.add(args.c_kzg)
    root = args.source.resolve()
    for path in (root/'common/tests/reference/c-kzg').iterdir():
        if path.is_file() and path.suffix in ('.toml', '.lock', '.rs'):
            capture.add(path, Path('source')/path.relative_to(root))
    source = root/'examples/projects/eip4844/main.zkc'
    entry = {'commitment': 'BlobToCommitment', 'opening': 'ComputeKzgProof', 'point': 'KzgProof',
             'blob': 'BlobProof', 'batch': 'BlobBatchProof'}[case.api]
    program = Program(source.read_text(), [], entry=f'example::{entry}',
                      dependencies=('constructions.ethereum.eip4844',), support=(source,))
    directory, package = compile_program(args, output, capture, manifest, case, program)
    data, expected = inputs(args, output, capture, manifest, case.count)
    raw = json.loads((data/'reference-inputs.json').read_text())

    def pinned(name):
        # SDK directory capabilities intentionally forbid ../ references.
        path = directory/name
        path.write_bytes((data/name).read_bytes())
        capture.add(path)
        return {'file': name, 'sha256': digest(path)}

    setup = pinned('setup.zkcv')
    base = {'package': str(package), 'sha256': digest(package), 'ingress': args.ingress}
    reference = {'kind': 'c_kzg', 'api': case.api, 'setup': str(root/'libraries/constructions/ethereum/eip4844/trusted_setup.txt'),
                 'inputs': str(data/'reference-inputs.json')}
    is_function = case.api in ('commitment', 'opening')
    if is_function:
        arguments = {'blob': pinned('blob.zkcv'), 'setup': setup}
        if case.api == 'opening': arguments['z'] = list(bytes.fromhex(raw['z']))
        path = directory/'arguments.json'
        write_json(path, {'inputs': {'P': arguments}})
        fields = ({'commitment': list(bytes.fromhex(expected['commitments'][0]))} if case.api == 'commitment'
                  else {k: list(bytes.fromhex(expected[k])) for k in ('point_proof', 'y')})
        if 'point_proof' in fields: fields['proof'] = fields.pop('point_proof')
        result = directory/'expected-output.json'
        write_json(result, {'format': 'zkc.entry-outputs/0', 'value': {'P': fields}})
        for file in (path, result): capture.add(file)
        backends = [('zkc', args.worker, base | {'kind': 'run', 'arguments': str(path),
                    'check': {'kind': 'output', 'expected': str(result)}}, 'admitted_function_call'),
                    ('reference', args.c_kzg, reference | {'expected': str(result)}, 'reference_kzg_call')]
        jobs = [Job(case.identifier, name, 'run', tool, backend, directory/'unused', boundary)
                for name, tool, backend, boundary in backends]
        for job in jobs: execute_job(job, directory/f'control-{job.implementation}', CONTROL, args.timeout)
        # Both clients must actually check the expected result on every call.
        wrong = directory/'incorrect-output.json'
        write_json(wrong, {'format': 'zkc.entry-outputs/0', 'value': {'P': {}}})
        capture.add(wrong)
        for job in jobs:
            backend = (job.backend | {'check': {'kind': 'output', 'expected': str(wrong)}}
                       if job.implementation == 'zkc' else job.backend | {'expected': str(wrong)})
            request = directory/f'incorrect-{job.implementation}.json'
            write_json(request, {'format': 'zkc.benchmark-job/0', 'backend': backend,
                                'operation': 'run', 'plan': CONTROL, 'proof': str(directory/'unused')})
            record = Journal(directory/f'incorrect-{job.implementation}', args.timeout).command(
                [job.executable, request], cwd=directory, expected=None)
            require(record['returncode'] > 0 and read_report(record).get('status') == 'incorrect-result',
                    'incorrect function output did not fail its result gate')
        check = None
    else:
        if case.api == 'point':
            public = {k: list(bytes.fromhex(v)) for k, v in {
                'commitment': expected['commitments'][0], 'z': raw['z'], 'y': expected['y']}.items()}
        elif case.api == 'blob':
            public = {'blob': pinned('blob.zkcv'), 'commitment': list(bytes.fromhex(expected['commitments'][0]))}
        else:
            public = {'blobs': pinned('blobs.zkcv'), 'commitments': list(b''.join(
                bytes.fromhex(p) for p in expected['commitments'])), 'count': str(case.count)}
        public_path, private_path = directory/'public.json', directory/'witness.json'
        write_json(public_path, public)
        write_json(private_path, {'setup': setup})
        for path in (public_path, private_path): capture.add(path)
        proof = data/('point.proof' if case.api == 'point' else 'blob.proof')
        source_backend = base | {'kind': 'host', 'inputs': [{'public': str(public_path), 'witness': str(private_path)}],
                                'preparation': args.preparation != 'disabled',
                                'preparation_entries': args.preparation_entries, 'preparation_bytes': args.preparation_bytes}
        source_jobs = [('zkc', source_backend)]
        if args.preparation == 'both': source_jobs.append(('unprepared', source_backend | {'preparation': False}))
        operations = ('verify',) if case.api == 'point' else ('prove', 'verify')
        jobs = [Job(case.identifier, name, op, args.worker, backend, proof, 'admitted_entry_call')
                for name, backend in source_jobs for op in operations]
        jobs += [Job(case.identifier, 'reference', op, args.c_kzg, reference | {'expected': str(proof)},
                     proof, 'reference_kzg_call') for op in operations]
        for job in jobs:
            result = execute_job(job, directory/f'control-{job.implementation}-{job.operation}', CONTROL, args.timeout)
            if job.operation == 'prove':
                require(Path(result['proof']['path']).read_bytes() == proof.read_bytes(), 'EIP-4844 proof bytes differ')

        for label, bytes_ in (('truncated', proof.read_bytes()[:-1]), ('trailing', proof.read_bytes()+b'\x00')):
            path = directory/f'{label}.proof'
            path.write_bytes(bytes_)
            capture.add(path)
            for job in jobs:
                if job.operation == 'verify':
                    refuse(replace(job, proof=path), directory/f'{label}-{job.implementation}', args.timeout,
                           truncated=label == 'truncated')
        # Change a well-formed mathematical statement, so failure is not a codec error.
        changed = dict(public)
        changed_reference = dict(raw)
        if case.api == 'point':
            y = ((int(raw['y'], 16)+1) % MODULUS).to_bytes(32, 'big')
            changed['y'], changed_reference['y'] = list(y), y.hex()
        else:
            payload = bytearray(Path(raw['blobs'][0]).read_bytes())
            payload[31] ^= 1
            raw_path = directory/'changed-blob.bin'
            raw_path.write_bytes(payload)
            capture.add(raw_path)
            changed_reference['blobs'] = [str(raw_path), *raw['blobs'][1:]]
            combined = bytes(payload) + b''.join(Path(p).read_bytes() for p in raw['blobs'][1:])
            path = directory/'changed.zkcv'
            path.write_bytes(frame(70, combined))
            capture.add(path)
            changed['blob' if case.api == 'blob' else 'blobs'] = {'file': path.name, 'sha256': digest(path)}
        changed_public, changed_input = directory/'changed.json', directory/'changed-reference.json'
        write_json(changed_public, changed)
        write_json(changed_input, changed_reference)
        for path in (changed_public, changed_input): capture.add(path)
        for job in jobs:
            if job.operation != 'verify': continue
            backend = (job.backend | {'inputs': [{'public': str(changed_public)}]}
                       if job.implementation != 'reference' else job.backend | {'inputs': str(changed_input)})
            refuse(replace(job, backend=backend), directory/f'changed-{job.implementation}', args.timeout)

        def check(job, path, target, _index):
            require(path.read_bytes() == proof.read_bytes(), 'timed EIP-4844 proof bytes differ')
            other = next(j for j in jobs if j.operation == 'verify'
                         and (j.implementation == 'reference') != (job.implementation == 'reference'))
            execute_job(replace(other, proof=path), target, CONTROL, args.timeout)

    manifest['contracts'][case.identifier] = {
        'family': 'Ethereum EIP-4844', 'api': case.api, 'blobs': case.count, 'field_elements_per_blob': 4096,
        'setup_sha256': SETUP_SHA256, 'input_policy': 'distinct deterministic SHA-256-derived full-width canonical scalars',
        'input_identity': {'blobs': [digest(Path(p)) for p in raw['blobs']],
                           'z': raw['z'], 'reference_outputs': expected},
        'boundaries': {j.implementation: j.boundary for j in jobs},
        'notes': ['Source uses the ordinary authored library, checked Kernel/Native selection and Host defaults.',
                  'Source includes source-level statement/setup validation, input adaptation, provider conversions, execution, publication and teardown.',
                  'Reference loads trusted setup once outside timing; precompute=0. Every output check is outside both execution timers.',
                  'Source admission includes Package::capture, reported separately from admission. JSON decode parses documents and resolves deferred references.',
                  'Source JSON execution includes deferred payload reads, pin verification and native imports. Preowned ingress materializes these during input construction; reference input decoding occurs before its execution timer.',
                  'Batch proving is sequential ordinary blob proof generation in both implementations; reference batch verification is one c-kzg API call.',
                  'RAYON_NUM_THREADS does not make the single-threaded c-kzg EIP-4844 API parallel.',
                  'Current compiler has no selectable all-Arkworks target policy; pre-preference compiler baselines must be explicit captured tools.'],
    }
    manifest.setdefault('comparisons', []).extend({'case': case.identifier, 'operation': op,
        'numerator': 'zkc', 'denominator': 'reference'} for op in {j.operation for j in jobs})
    manifest['checks'].append({'case': case.identifier, 'status': 'passed',
                               'oracle': 'pinned c-kzg byte equality, every result and cross-verified timed proofs',
                               'controls': ['incorrect output'] if is_function else ['changed statement', 'truncated proof', 'trailing proof']})
    return jobs, check
