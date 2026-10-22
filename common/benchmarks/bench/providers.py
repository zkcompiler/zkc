"""Matched provider arithmetic, conversion and installed-operation controls."""
from dataclasses import dataclass

from .io import require
from .runner import CONTROL, Job, execute_job

BOUNDARIES = {'resident': 'resident_kernel_call', 'converted': 'converted_kernel_call',
              'import': 'provider_import', 'export': 'provider_export',
              'installed': 'installed_operation_call'}


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
            'resident': 'arithmetic and result construction; native provider inputs prepared outside timer',
            'converted': 'input import, arithmetic, output export and temporary destruction',
            'installed': 'VM local call, Native admission, conversion, arithmetic and output publication; Runner construction excluded',
            'import': 'canonical point and scalar import including subgroup checks; no arithmetic',
            'export': 'canonical point export including subgroup checks; no arithmetic',
        }[shape['boundary']],
        'excluded': ['deterministic input generation', 'correctness oracle', 'JSON I/O', 'independent result check', 'returned result destruction'],
        'notes': ['Arkworks uses existing automatic batch normalization.',
                  'blst internal threads disabled; MSM is variable-time.',
                  'No protocol throughput or security claim.'],
    }
    if len(jobs) == 2:
        manifest.setdefault('comparisons', []).append(
            {'case': case.identifier, 'operation': 'run', 'numerator': 'blst', 'denominator': 'arkworks'})
    manifest['checks'].append({'case': case.identifier, 'status': 'passed',
                               'oracle': 'every timed result compared with Arkworks outside timer'})
    return jobs, None
