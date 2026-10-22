"""Matched provider arithmetic, conversion and installed-operation controls."""
from dataclasses import dataclass

from .io import require
from .runner import CONTROL, Job, execute_job

BOUNDARIES = {'resident': 'resident_kernel_call', 'converted': 'converted_kernel_call',
              'import': 'provider_import', 'export': 'provider_export',
              'installed': 'installed_operation_call',
              'resident_installed_chain': 'resident_installed_chain',
              'wire_resident_chain': 'wire_decode_resident_execute_wire_encode'}


@dataclass(frozen=True)
class Case:
    identifier: str
    shape: dict
    name: str = 'bls_provider'


def catalog():
    cases = []
    for group in ('g1', 'g2', 'pairing'):
        kernels = ('pairing_check',) if group == 'pairing' else ('scale', 'scale_each', 'vector_scale', 'msm')
        for kernel in kernels:
            sizes = (1,) if kernel == 'scale' else (2, 8, 32) if group == 'pairing' else (32, 256, 1024)
            for n in sizes:
                for boundary in ('resident', 'converted', 'installed'):
                    shape = {'group': group, 'kernel': kernel, 'elements': n, 'boundary': boundary}
                    name = f'provider-{group}-{kernel.replace("_", "-")}-{boundary}-{n}'
                    cases.append((name, Case(name, shape), shape))
        if group != 'pairing':
            for n in (1, 32, 256, 1024):
                for boundary in ('import', 'export'):
                    shape = {'group': group, 'kernel': 'msm', 'elements': n, 'boundary': boundary}
                    name = f'provider-{group}-{boundary}-{n}'
                    cases.append((name, Case(name, shape), shape))
    for group in ('scalar', 'g1', 'g2', 'pairing'):
        kernels = (('field_mul', 'vector_mul') if group == 'scalar' else
                   ('pairing_check',) if group == 'pairing' else
                   ('scale', 'scale_each', 'vector_scale', 'msm'))
        for kernel in kernels:
            sizes = ((1,) if kernel in ('scale', 'field_mul') else
                     (2, 32) if group == 'pairing' else (1, 32, 1024))
            boundaries = (('resident', 'converted', 'installed', 'resident_installed_chain', 'wire_resident_chain')
                          if group == 'scalar' else ('resident_installed_chain', 'wire_resident_chain'))
            for n in sizes:
                for boundary in boundaries:
                    shape = {'group': group, 'kernel': kernel, 'elements': n, 'boundary': boundary}
                    if boundary in ('resident_installed_chain', 'wire_resident_chain'):
                        shape['chain_length'] = 4
                    name = f'provider-{group}-{kernel.replace("_", "-")}-{boundary.replace("_", "-")}-{n}'
                    cases.append((name, Case(name, shape), shape))
                for boundary in ('resident', 'converted'):
                    shape = {'group': group, 'kernel': kernel, 'elements': n,
                             'boundary': boundary, 'chain_length': 4}
                    name = f'provider-{group}-{kernel.replace("_", "-")}-{boundary}-chain-{n}'
                    cases.append((name, Case(name, shape), shape))
    return cases


def prepare_case(args, output, capture, manifest, case):
    require(not args.execution_counts, 'provider controls require an ordinary timing worker')
    directory = output / 'cases' / case.identifier
    shape = case.shape
    providers = ('blst',) if shape['boundary'] in ('import', 'export') else ('arkworks', 'blst')
    jobs = []
    for provider in providers:
        job = Job(case.identifier, provider, 'run', args.worker,
                  {'kind': 'kernel', 'provider': provider, **shape},
                  directory / 'unused.proof', BOUNDARIES[shape['boundary']])
        execute_job(job, directory / provider, CONTROL, args.timeout)
        jobs.append(job)
    manifest['contracts'][case.identifier] = {
        'family': 'BLS12-381 provider', 'shape': shape, 'threads': args.threads,
        'boundaries': {job.implementation: job.boundary for job in jobs},
        'input_policy': 'fixed full-width SHA-256-derived scalars; nontrivial generator multiples',
        'comparison': 'same mathematical operation and input values; explicit representation boundary',
        'included': {
            'resident': 'arithmetic chain and result construction; resident provider bulk inputs prepared outside timer',
            'converted': 'input import once, complete arithmetic chain, output export once and temporary destruction',
            'installed': 'VM local call, Native publication and Runner teardown; blst explicitly converts Ark inputs to resident, computes, converts output back; Runner construction excluded',
            'resident_installed_chain': 'repeated resident operations and Native publication through VM plus Runner teardown; selected values and Runner constructed before timer',
            'wire_resident_chain': 'selected wire decode, Runner construction, repeated resident execution, selected output wire encode and Runner teardown',
            'import': 'canonical point and scalar import including subgroup checks; no arithmetic',
            'export': 'canonical point export including subgroup checks; no arithmetic',
        }[shape['boundary']],
        'chain_length': shape.get('chain_length', 1),
        'memory_observation': 'managed retained payload and unavailable scratch peaks are separate from process lifetime peak RSS',
        'excluded': ['program admission and installation', 'backend construction', 'deterministic input generation', 'correctness oracle', 'JSON I/O', 'independent result check', 'returned result destruction'],
        'notes': ['Arkworks uses existing automatic batch normalization.',
                  'blst internal threads disabled; MSM explicitly authorizes variable-time execution in trusted deployment policy.',
                  'MSM chains accumulate repeated MSM outputs using resident curve.add; pairing chains return and check every Boolean.',
                  'Repeated pairing inputs cancel nonidentity pairs (true product for even sizes); existing single-call controls retain nontrivial false products.',
                  'Input/output codecs use Native selected physical types; conversion diagnostics describe reached explicit program occurrences.',
                  'No protocol throughput or security claim.'],
    }
    if len(jobs) == 2:
        manifest.setdefault('comparisons', []).append(
            {'case': case.identifier, 'operation': 'run', 'numerator': 'blst', 'denominator': 'arkworks'})
    manifest['checks'].append({'case': case.identifier, 'status': 'passed',
                               'oracle': 'every timed result compared with Arkworks outside timer'})
    return jobs, None


def _installed_fixture(backend):
    """Expected straight-line benchmark fixture, independent of worker receipts.

    This checks the bounded measurement workload, not general Program admission.
    The worker independently admits the program and checks its numerical result.
    """
    group, kernel = backend['group'], backend['kernel']
    length, n = backend.get('chain_length', 1), backend['elements']
    selected = backend['provider']

    def physical(kind, provider):
        domain = 'bls12-381.fr' if kind in ('field', 'vector') else f'bls12-381.{group}'
        if kind == 'bool':
            return 'bool@native.bool/0'
        if kind in ('g1s', 'g2s'):
            domain, kind = f'bls12-381.{kind[:2]}', 'groups'
        if provider == 'blst':
            representation = 'fr' if kind in ('field', 'vector') else domain.rsplit('.', 1)[1]
            representation = f'blst/{representation}'
        else:
            representation = {'field': 'fr', 'vector': 'fr-vector',
                              'group': 'g1' if domain.endswith('.g1') else 'bls12-381-g2',
                              'groups': 'g1-vector' if domain.endswith('.g1') else 'bls12-381-g2-vector'}[kind]
            representation = f'arkworks.{representation}/0'
        return f'{kind}:{domain}@{representation}'

    contract, kinds, result_kind = {
        'field_mul': ('field.mul', ('field', 'field'), 'field'),
        'vector_mul': ('vector.mul', ('vector', 'vector'), 'vector'),
        'scale': ('curve.scale', ('group', 'field'), 'group'),
        'scale_each': ('curve.scale_each', ('vector', 'groups'), 'groups'),
        'vector_scale': ('curve.vector_scale', ('groups', 'field'), 'groups'),
        'msm': ('curve.msm', ('vector', 'groups'), 'group'),
        'pairing_check': ('pairing.check', ('g1s', 'g2s'), 'bool'),
    }[kernel]
    domain = 'bls12-381.fr' if group in ('scalar', 'pairing') else f'bls12-381.{group}'
    owner = 'blst/resident' if selected == 'blst' else 'arkworks'
    port_provider = 'arkworks' if backend['boundary'] == 'installed' else selected
    inputs = [physical(kind, port_provider) for kind in kinds]
    selected_inputs = [physical(kind, selected) for kind in kinds]
    output = physical(result_kind, port_provider)
    selected_output = physical(result_kind, selected)
    bindings, body, conversions = [], [], []

    def call(operation, arguments, implementation, parameters, values):
        declaration = [operation, arguments, implementation, parameters]
        slot = next((i for i, row in enumerate(bindings) if row[1:] == declaration), len(bindings))
        if slot == len(bindings):
            bindings.append([f'b{slot}', *declaration])
        name = f'v{len(body)}'
        body.append(['op', f'site{len(body)}', f'b{slot}', [], values, [name]])
        return name

    def convert(value, source, target):
        if source == target:
            return value
        logical = source.split('@')[0]
        elements = n if logical.startswith(('vector:', 'groups:')) else 1
        width = 96 if logical.endswith('.g2') else 48 if logical.endswith('.g1') else 32
        conversions.append(dict(logical_type=logical, source=source, target=target,
                                calls=1, elements=elements, canonical_payload_bytes=elements * width))
        return call('representation.convert', [logical], 'native/representation.convert', [source, target], [value])

    names = [f'a{i}' for i in range(len(inputs))]
    operands = [convert(name, source, target) for name, source, target in zip(names, inputs, selected_inputs)]
    original, result, results = list(operands), None, []
    for _ in range(length):
        following = call(contract, [domain], f'{owner}/{contract}', [], list(operands))
        result = (call('curve.add', [domain], f'{owner}/curve.add', [], [result, following])
                  if result is not None and kernel == 'msm' else following)
        if kernel in ('scale', 'vector_scale', 'field_mul', 'vector_mul'):
            operands[0] = result
        elif kernel == 'scale_each':
            operands[1] = result
        elif kernel == 'pairing_check':
            results.append(result)
        else:
            operands = list(original)
    if kernel != 'pairing_check':
        results.append(result)
    results = [convert(value, selected_output, output) for value in results]
    outputs = [output] * len(results)
    ports = [[name, ty] for name, ty in zip(names, inputs)]
    body.append(['return', results])
    program = ['zkc.program/0', bindings,
               [['function', 'f', ports, outputs, body, ['f', []]]],
               [['participant', 'actor', 'instance', 'P', ports, outputs,
                 [['local', 'work', 'f', names, results], ['return', results]], []]],
               [['entry', 'main', [['P', 'actor']]]]]
    return program, inputs, outputs, conversions


def validate_evidence(report, backend):
    """Check provider boundary receipts in live and retained worker results."""
    if backend['kind'] != 'kernel' or backend['boundary'] not in (
            'installed', 'resident_installed_chain', 'wire_resident_chain'):
        return
    evidence = report.get('diagnostics')
    require(isinstance(evidence, dict), 'missing installed provider evidence')
    length = backend.get('chain_length', 1)
    require(evidence.get('provider') == backend['provider']
            and type(evidence.get('chain_length')) is int and evidence['chain_length'] == length,
            'provider evidence differs from the request')
    calls = length + (length - 1 if backend['kernel'] == 'msm' else 0)
    require(type(evidence.get('arithmetic_calls')) is int and evidence['arithmetic_calls'] == calls,
            'provider arithmetic count differs from the requested chain')
    policy = evidence.get('trusted_timing_authorization')
    require(policy == {'allow_unspecified_timing': True, 'allow_variable_time': backend['kernel'] == 'msm'},
            'provider timing authorization differs from the workload')
    program, inputs, outputs, conversions = _installed_fixture(backend)
    require(evidence.get('input_physical_types') == inputs
            and evidence.get('output_physical_types') == outputs,
            'provider physical ports differ from the requested workload')
    require(evidence.get('program') == program,
            'retained provider program differs from the requested workload')
    observed = evidence.get('explicit_conversions')
    require(observed == conversions
            and all(all(type(row[name]) is int for name in
                        ('calls', 'elements', 'canonical_payload_bytes')) for row in observed),
            'conversion receipts differ from reached workload occurrences')
    managed = evidence.get('managed')
    require(isinstance(managed, dict) and type(managed.get('input_retained_payload_bytes')) is int
            and managed['input_retained_payload_bytes'] >= 0
            and isinstance(managed.get('terminal_runner_usage'), dict), 'missing managed payload observations')
    for name in ('peak_retained_payload_bytes', 'peak_scratch_bytes'):
        require(name in managed and (managed[name] is None or type(managed[name]) is int and managed[name] >= 0),
                'invalid managed high-water observation')
    for name in ('input_wire_bytes', 'output_wire_bytes'):
        require(type(evidence.get(name)) is int and evidence[name] > 0, 'invalid provider wire byte count')
