"""Matched provider arithmetic, conversion and installed-operation controls."""
from dataclasses import dataclass

from .io import require
from .runner import CONTROL, Job, execute_job

BOUNDARIES = {'resident': 'resident_kernel_call', 'converted': 'converted_kernel_call',
              'import': 'provider_import', 'export': 'provider_export',
              'installed': 'installed_operation_call',
              'resident_installed_chain': 'resident_installed_chain',
              'wire_resident_chain': 'wire_decode_resident_execute_wire_encode'}
FAMILIES = {'bls12-381': ('arkworks', 'blst'), 'bn254': ('arkworks', 'halo2curves-axiom')}


def validate_backend(backend, boundary=None, operation=None):
    """Positive family/provider inventory shared by live and retained jobs."""
    required = {'kind', 'provider', 'group', 'kernel', 'boundary', 'elements'}
    require(isinstance(backend, dict) and backend.get('kind') == 'kernel'
            and required <= backend.keys() and not backend.keys() - required - {'family', 'chain_length'},
            'invalid backend fields')
    family = backend.get('family', 'bls12-381')
    require(isinstance(family, str) and family in FAMILIES
            and backend['provider'] in FAMILIES[family], 'invalid provider family')
    require(all(isinstance(backend[key], str) for key in ('provider', 'group', 'kernel', 'boundary'))
            and backend['group'] in ('scalar', 'g1', 'g2', 'pairing')
            and backend['kernel'] in ('field_mul', 'vector_mul', 'scale', 'scale_each', 'vector_scale', 'msm', 'pairing_check')
            and backend['boundary'] in BOUNDARIES, 'invalid kernel control')
    require(boundary is None or boundary == BOUNDARIES[backend['boundary']], 'invalid kernel boundary')
    require(operation in (None, 'run'), 'invalid kernel operation')
    require(type(backend['elements']) is int and 1 <= backend['elements'] <= 4096, 'invalid kernel length')
    require((backend['group'] == 'pairing') == (backend['kernel'] == 'pairing_check')
            and (backend['group'] == 'scalar') == (backend['kernel'] in ('field_mul', 'vector_mul'))
            and (backend['kernel'] not in ('scale', 'field_mul') or backend['elements'] == 1)
            and (backend['boundary'] not in ('import', 'export')
                 or backend['provider'] == FAMILIES[family][1] and backend['group'] in ('g1', 'g2')),
            'unsupported kernel control')
    require(family != 'bn254' or backend['kernel'] in ('field_mul', 'vector_mul', 'scale', 'msm', 'pairing_check'),
            'unsupported BN254 kernel control')
    length = backend.get('chain_length', 1)
    require(type(length) is int and 1 <= length <= 32
            and (length == 1 or backend['boundary'] in ('resident', 'converted', 'resident_installed_chain', 'wire_resident_chain')),
            'invalid provider chain length')


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
    return cases + _bn254_catalog()


def _bn254_catalog():
    cases = []
    for group, kernel, sizes in (('scalar', 'field_mul', (1,)), ('scalar', 'vector_mul', (32, 256)),
                                 ('g1', 'scale', (1,)), ('g2', 'scale', (1,)),
                                 ('g1', 'msm', (32, 256)), ('g2', 'msm', (32, 256)),
                                 ('pairing', 'pairing_check', (2, 8))):
        for n in sizes:
            for boundary, length in (('resident', 1), ('converted', 1), ('installed', 1),
                                     ('resident', 4), ('converted', 4),
                                     ('resident_installed_chain', 4), ('wire_resident_chain', 4)):
                shape = dict(family='bn254', group=group, kernel=kernel, elements=n, boundary=boundary)
                if length != 1:
                    shape['chain_length'] = length
                suffix = '-chain' if length != 1 and boundary in ('resident', 'converted') else ''
                name = f'provider-bn254-{group}-{kernel.replace("_", "-")}-{boundary.replace("_", "-")}{suffix}-{n}'
                cases.append((name, Case(name, shape, 'bn254_provider'), shape))
    for group in ('g1', 'g2'):
        for n in (1, 32, 256):
            for boundary in ('import', 'export'):
                shape = dict(family='bn254', group=group, kernel='msm', elements=n, boundary=boundary)
                name = f'provider-bn254-{group}-{boundary}-{n}'
                cases.append((name, Case(name, shape, 'bn254_provider'), shape))
    return cases


def prepare_case(args, output, capture, manifest, case):
    require(not args.execution_counts, 'provider controls require an ordinary timing worker')
    directory = output / 'cases' / case.identifier
    shape = case.shape
    family = shape.get('family', 'bls12-381')
    pair = FAMILIES[family]
    providers = pair[1:] if shape['boundary'] in ('import', 'export') else pair
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
    if family == 'bn254':
        contract = manifest['contracts'][case.identifier]
        contract['family'] = 'BN254 provider'
        contract['input_policy'] = 'fixed domain-separated full-width SHA-256-derived nonzero scalars; nonidentity generator multiples'
        if shape['boundary'] == 'installed':
            contract['included'] = ('VM local call, Native publication and Runner teardown; halo2curves-axiom explicitly '
                                    'imports Arkworks BN254 inputs, computes and exports output; Runner construction excluded')
        contract['notes'] = [
            'Arkworks BN254 and halo2curves-axiom BN254 receive the same mathematical values and operation chain.',
            'Arkworks MSM stages affine bases; halo2curves-axiom resident MSM borrows upstream affine and scalar buffers.',
            'Arkworks converted cases are a zero-conversion baseline; the foreign provider imports once and exports once.',
            'halo2curves-axiom uses serial MSM; installed MSM explicitly authorizes variable-time execution.',
            'MSM chains add repeated MSM outputs; pairing chains return and check every Boolean.',
            'Single-call pairing controls use nontrivial false products; repeated even-size controls cancel nonidentity pairs.',
            'Installed boundaries admit the actual Native physical types and use nominal BN254 ZKCV frames; no compiler path is measured.',
            'Direct adapter receipts count per-element calls; installed conversion receipts count reached program occurrences.',
            'Provider scheduling scores and workspace admission bounds are separate from observed VM logical bytes and unavailable scratch peaks.',
            'Pairing includes preparation, Miller loop and final exponentiation on every call; no prepared cache is measured.',
            'No protocol throughput, cross-curve equivalence or security claim.',
        ]
    if len(jobs) == 2:
        manifest.setdefault('comparisons', []).append(
            {'case': case.identifier, 'operation': 'run', 'numerator': pair[1], 'denominator': 'arkworks'})
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
    family = backend.get('family', 'bls12-381')

    def physical(kind, provider):
        domain = f'{family}.fr' if kind in ('field', 'vector') else f'{family}.{group}'
        if kind == 'bool':
            return 'bool@native.bool/0'
        if kind in ('g1s', 'g2s'):
            domain, kind = f'{family}.{kind[:2]}', 'groups'
        if provider == 'blst':
            representation = 'fr' if kind in ('field', 'vector') else domain.rsplit('.', 1)[1]
            representation = f'blst/{representation}'
        elif provider == 'halo2curves-axiom':
            representation = f'halo2curves-axiom/{domain}'
        elif family == 'bn254':
            suffix = {'field': 'fr', 'vector': 'fr-vector',
                      'group': domain.rsplit('.', 1)[1],
                      'groups': f'{domain.rsplit(".", 1)[1]}-vector'}[kind]
            representation = f'arkworks.bn254-{suffix}/0'
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
    domain = f'{family}.fr' if group in ('scalar', 'pairing') else f'{family}.{group}'
    owner = 'arkworks' if selected == 'arkworks' else f'{selected}/resident'
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
        width = _payload_width(logical)
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


def _payload_width(logical):
    if logical.endswith('.g2'):
        return 64 if ':bn254.' in logical else 96
    if logical.endswith('.g1'):
        return 32 if ':bn254.' in logical else 48
    return 32


def _direct_conversions(backend):
    _, inputs, outputs, _ = _installed_fixture(backend | {'boundary': 'resident'})
    _, canonical_inputs, canonical_outputs, _ = _installed_fixture(backend | {'provider': 'arkworks', 'boundary': 'resident'})
    pairs = []
    boundary = backend['boundary']
    if backend['provider'] != 'arkworks':
        if boundary in ('converted', 'import'):
            pairs.extend(zip(canonical_inputs, inputs))
        if boundary == 'converted':
            # Repeated pairing returns Booleans; arithmetic returns one value.
            pairs.extend(zip(outputs, canonical_outputs))
        if boundary == 'export':
            pairs.extend((source, target) for source, target in zip(inputs, canonical_inputs)
                         if source.startswith(('group:', 'groups:')))
    conversions = []
    for source, target in pairs:
        if source == target:
            continue
        logical = source.split('@')[0]
        n = backend['elements'] if logical.startswith(('vector:', 'groups:')) else 1
        row = dict(source=source, target=target, calls=n, elements=n,
                   canonical_payload_bytes=n * _payload_width(logical))
        if backend.get('family', 'bls12-381') == 'bn254':
            row['logical_type'] = logical
        conversions.append(row)
    return conversions


DIRECT_STORAGE = {
    'arkworks': 'Arkworks owned scalar/affine buffers; resident calls borrow Arkworks mathematical storage',
    'blst': 'blst resident upstream ScalarVector/G1Vector/G2Vector; no wrapper-vector reconstruction in timed resident calls',
    'halo2curves-axiom': 'halo2curves-axiom owned Fr/G1Affine/G2Affine buffers; resident calls borrow upstream ABI storage',
}


def _validate_direct(report, backend):
    evidence = report.get('diagnostics')
    require(isinstance(evidence, dict)
            and evidence.get('family') == backend.get('family', 'bls12-381')
            and evidence.get('provider') == backend['provider'], 'missing direct provider evidence')
    length = backend.get('chain_length', 1)
    conversion = backend['boundary'] in ('import', 'export')
    calls = 0 if conversion else length + (length - 1 if backend['kernel'] == 'msm' else 0)
    require(type(evidence.get('chain_length')) is int and evidence['chain_length'] == length
            and type(evidence.get('arithmetic_calls')) is int and evidence['arithmetic_calls'] == calls,
            'direct provider chain differs from the request')
    observed = evidence.get('kernel_adapter_conversions')
    require(observed == _direct_conversions(backend)
            and all(all(type(row[name]) is int for name in ('calls', 'elements', 'canonical_payload_bytes'))
                    for row in observed), 'adapter receipts differ from the requested boundary')
    require(evidence.get('bulk_storage') == DIRECT_STORAGE[backend['provider']],
            'direct provider storage differs from the request')
    managed = evidence.get('managed')
    require(isinstance(managed, dict) and all(key in managed and managed[key] is None
            for key in ('peak_retained_payload_bytes', 'peak_scratch_bytes')),
            'invalid direct managed high-water observation')
    bounded = backend['provider'] != 'arkworks' and backend['kernel'] in ('msm', 'pairing_check') and not conversion
    bound = managed.get('provider_workspace_admission_bound_bytes_per_call')
    require('provider_workspace_admission_bound_bytes_per_call' in managed
            and (type(bound) is int and bound > 0 if bounded else bound is None),
            'invalid direct provider admission bound')


def _validate_bn254(report, backend):
    evidence = report.get('diagnostics')
    require(isinstance(evidence, dict) and evidence.get('family') == 'bn254'
            and evidence.get('provider') == backend['provider'], 'missing BN254 provider evidence')
    length = backend.get('chain_length', 1)
    conversion = backend['boundary'] in ('import', 'export')
    calls = 0 if conversion else length + (length - 1 if backend['kernel'] == 'msm' else 0)
    require(type(evidence.get('chain_length')) is int and evidence['chain_length'] == length
            and type(evidence.get('arithmetic_calls')) is int and evidence['arithmetic_calls'] == calls,
            'BN254 provider chain differs from the request')
    installed = backend['boundary'] in ('installed', 'resident_installed_chain', 'wire_resident_chain')
    if not installed:
        observed = evidence.get('kernel_adapter_conversions')
        require(observed == _direct_conversions(backend)
                and all(all(type(row[name]) is int for name in ('calls', 'elements', 'canonical_payload_bytes'))
                        for row in observed), 'BN254 adapter receipts differ from the requested boundary')
    managed = evidence.get('managed')
    require(isinstance(managed, dict), 'missing BN254 resource observations')
    for key in ('peak_retained_payload_bytes', 'peak_scratch_bytes'):
        require(key in managed and managed[key] is None,
                'invalid BN254 managed high-water observation')
    bounded = backend['provider'] == 'halo2curves-axiom' and backend['kernel'] in ('msm', 'pairing_check') and not conversion
    bound = managed.get('provider_workspace_admission_bound_bytes_per_call')
    score = evidence.get('provider_scheduling_work_units_per_arithmetic_call')
    require('provider_workspace_admission_bound_bytes_per_call' in managed
            and 'provider_scheduling_work_units_per_arithmetic_call' in evidence
            and (type(bound) is int and bound > 0 and type(score) is int and score > 0
                 if bounded else bound is None and score is None), 'invalid BN254 provider admission bounds')
    if installed:
        policy = evidence.get('trusted_timing_authorization')
        require(isinstance(policy, dict) and all(type(value) is bool for value in policy.values()),
                'invalid BN254 timing authorization')
        usage = managed.get('terminal_runner_usage')
        fields = {'instructions', 'iterations', 'live_values', 'live_retained_payload_bytes',
                  'cumulative_fresh_payload_bytes', 'logical_bytes'}
        require(isinstance(usage, dict) and usage.keys() == fields
                and all(type(value) is int and value >= 0 for value in usage.values())
                and usage['instructions'] > 0 and usage['logical_bytes'] > 0,
                'missing BN254 terminal VM resource charges')
        _, inputs, outputs, _ = _installed_fixture(backend)
        def wire(physical):
            logical = physical.split('@')[0]
            if logical == 'bool':
                return 5, 7
            kind, domain = logical.split(':')
            tag = {('field', 'bn254.fr'): 40, ('vector', 'bn254.fr'): 41,
                   ('group', 'bn254.g1'): 46, ('groups', 'bn254.g1'): 47,
                   ('group', 'bn254.g2'): 48, ('groups', 'bn254.g2'): 49}[kind, domain]
            width = _payload_width(logical)
            return tag, 10 + backend['elements'] * width if kind in ('vector', 'groups') else 6 + width
        for name, types in (('input', inputs), ('output', outputs)):
            frames = [wire(ty) for ty in types]
            tags = evidence.get(f'{name}_wire_tags')
            require(tags == [tag for tag, _ in frames] and all(type(tag) is int for tag in tags)
                    and type(evidence.get(f'{name}_wire_bytes')) is int
                    and evidence[f'{name}_wire_bytes'] == sum(size for _, size in frames),
                    'BN254 wire evidence differs from nominal ZKCV frames')


def validate_evidence(report, backend):
    """Check provider boundary receipts in live and retained worker results."""
    if backend['kind'] != 'kernel':
        return
    validate_backend(backend)
    if backend.get('family', 'bls12-381') == 'bn254':
        _validate_bn254(report, backend)
    if backend['boundary'] not in (
            'installed', 'resident_installed_chain', 'wire_resident_chain'):
        _validate_direct(report, backend)
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
