#!/usr/bin/env python3
"""Measure complete source protocols with explicitly selected, already built tools.

Only this tool's output directory is written. No builds or dependency downloads
are performed. See protocol-math.md for measurement boundaries and reproduction.
"""

import argparse
from collections import Counter, defaultdict
import csv
import json
import os
from pathlib import Path
import platform
import re
import shutil
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from processes import positive_timeout  # noqa: E402
sys.path.insert(0, str(ROOT / 'common/tests/support'))
from project import project_inputs  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bench.io import (  # noqa: E402
    Journal, MeasurementError, digest, executable, identity,
    positive_integer, require, write_json)

FORMAT = 'zkc.protocol-measurement/0'
P = 2130706433
POLICIES = {'default': [], 'no-finite-bulk': ['--no-finite-bulk'],
            'release-storage': ['--release-storage']}
COUNTERS = ('instructions', 'iterations', 'logical_bytes', 'total_value_bytes',
            'ring_work', 'external_work')
EXIT_COUNTERS = ('live_values', 'live_value_bytes', 'live_resource_units',
                 'retained_output_units')


def case_catalog():
    cases = []
    for size, rounds in [(32, 3), (64, 4), (1024, 6)]:
        cases.append({'name': f'fri-{size}', 'project': 'fri', 'entry': 'example::Proof',
                      'size': size, 'rounds': rounds,
                      'replacement': ['LowDegree<Rows,5,0,3,8>',
                                      f'LowDegree<Rows,{size.bit_length()-1},0,{rounds},8>']})
    for size in (32, 64, 1024):
        cases.append({'name': f'air-stark-{size}', 'project': 'air-stark',
                      'entry': 'air_stark_example::Proof', 'size': size,
                      'replacement': ['TableArgument<0,Recurrence,3,5,8,8>',
                                      f'TableArgument<0,Recurrence,3,{size.bit_length()-1},8,8>']})
    for reduction, entry in [('logup', 'ProofLogUp'), ('product', 'ProofProduct')]:
        for shape, fixture in [('absent', 'arithmetic-only'), ('present', 'store-load')]:
            cases.append({'name': f'machine-{reduction}-{shape}',
                          'project': 'accumulator-machine',
                          'entry': f'accumulator_machine::{entry}',
                          'fixture': fixture, 'memory_present': shape == 'present'})
    return cases


def project(root, name):
    directory = 'examples/projects' if name == 'fri' else 'common/tests/fixtures/projects'
    manifest = root / directory / name / 'zkc.toml'
    modules, assets = project_inputs(manifest)
    return manifest, modules, assets


def source_files(root, cases):
    paths = set()
    for case in cases:
        manifest, modules, assets = project(root, case['project'])
        manifests = []
        project_inputs(manifest, manifests=manifests)
        paths.update(manifests)
        paths.update([manifest, *modules.values(), *(v[1] for v in assets.values())])
        if case['project'] != 'fri':
            paths.add(manifest.parent / 'prepare.py')
        if case['project'] == 'air-stark':
            paths.add(root / 'compiler/adapters/plonky3/fixtures/recurrence/source-trace-honest.json')
        if case['project'] == 'accumulator-machine':
            adapter = root / 'compiler/adapters/accumulator-machine'
            paths.update([adapter / 'accumulator_machine.py', adapter.parent / 'ring_arena.py',
                          adapter / 'fixtures' / case['fixture'] / 'run.json'])
    for name in ('Cargo.lock', 'flake.lock', 'uv.lock', 'rust-toolchain.toml'):
        paths.add(root / name)
    for path in paths:
        require(path.is_relative_to(root) and path.is_file(), f'missing or external input: {path}')
    return sorted(paths)


def snapshot(root, destination, cases, journal, expected_revision=None):
    def git(*args):
        result = journal.command(['git', '-C', root, *args], cwd=root)
        return Path(result['stdout']).read_text().strip()
    revision = git('rev-parse', 'HEAD')
    if expected_revision:
        require(revision == git('rev-parse', f'{expected_revision}^{{commit}}'),
                f'baseline HEAD is {revision}, expected {expected_revision}')
    record = {'path': str(root), 'revision': revision, 'tree': git('rev-parse', 'HEAD^{tree}'),
              'status': git('status', '--short'), 'files': {}}
    for source in source_files(root, cases):
        relative = str(source.relative_to(root))
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        record['files'][relative] = digest(target)
        require(record['files'][relative] == digest(source), f'input changed during copy: {source}')
        if expected_revision:
            # HEAD alone does not prove a dirty worktree is the original baseline.
            result = journal.command(['git', '-C', root, 'show', f'{revision}:{relative}'], cwd=root)
            require(digest(Path(result['stdout'])) == digest(target),
                    f'baseline input differs from {revision}: {relative}')
    return record


def extension_multiply(left, right):
    coefficients = [0] * 15
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            coefficients[i + j] += a * b
    for k in range(14, 7, -1):
        coefficients[k - 8] += 3 * coefficients[k]
    return [x % P for x in coefficients[:8]]


def fri_inputs(size, rounds):
    """Independent polynomial evaluation in F_p[u]/(u^8-3), no runtime kernels."""
    shift = [3, 1, 0, 0, 0, 0, 0, 0]
    root = pow(1791270792, (1 << 24) // size, P)
    require(pow(root, size, P) == 1 and pow(root, size // 2, P) == P - 1,
            'invalid two-adic root')
    coefficients = [[i + 1, i * i, 0, 0, 0, 0, 0, 1] for i in range(1 << rounds)]
    word = []
    for i in range(size):
        point = [x * pow(root, i, P) % P for x in shift]
        value = [0] * 8
        for coefficient in reversed(coefficients):
            value = [(a + b) % P for a, b in zip(extension_multiply(value, point), coefficient)]
        word.append(list(map(str, value)))
    return ({'shift': list(map(str, shift)), 'round_count': str(rounds), 'query_count': '8'},
            {'word': word})


def prepare_case(root, case, directory, journal):
    directory.mkdir(parents=True)
    manifest, modules, assets = project(root, case['project'])
    entry_module = case['entry'].split('::')[0]
    source = modules[entry_module].read_text()
    if 'replacement' in case:
        old, new = case['replacement']
        require(source.count(old) == 1, f'profile anchor must occur once: {old}')
        source = source.replace(old, new)
    entry_source = directory / 'main.zkc'
    entry_source.write_text(source)
    modules[entry_module] = entry_source
    flags = [f'--module={name}={path}' for name, path in sorted(modules.items())]
    flags += [f'--asset={name}={kind}={path}' for name, (kind, path) in sorted(assets.items())]
    if case['project'] == 'fri':
        public, witness = fri_inputs(case['size'], case['rounds'])
        write_json(directory / 'public.json', public)
        write_json(directory / 'witness.json', witness)
    else:
        command = [sys.executable, manifest.parent / 'prepare.py']
        if case['project'] == 'accumulator-machine':
            command += [root / 'compiler/adapters/accumulator-machine/fixtures' / case['fixture'] / 'run.json']
        command.append(directory)
        if case.get('memory_present'):
            command += ['--memory-clocks', '16', '--memory-present']
        journal.command(command, cwd=root)
    metadata = case | {'compiler_inputs': flags,
                       'files': {name: identity(directory / name)
                                 for name in ('main.zkc', 'public.json', 'witness.json')}}
    write_json(directory / 'case.json', metadata)
    return flags


def logical_inventory(source):
    """Static textual inventory of the compiler's generic-operation print form."""
    operations = Counter(re.findall(r'^\s*(?:%[^=\n]+ = )?"([\w.]+)"\(', source, re.M))
    require(operations.get('protocol.module') == 1, 'expected generic protocol IR')
    bindings = Counter()
    for line in source.splitlines():
        if '"local.binding"(' in line:
            match = re.search(r'contract = "([^"]+)"', line)
            require(match is not None, 'binding without a printed contract')
            bindings[match[1]] += 1
    return {'operations': dict(sorted(operations.items())),
            'binding_declarations': dict(sorted(bindings.items()))}


def kernel_inventory(package):
    artifact = json.loads(package['artifact'])
    require(isinstance(artifact, list) and len(artifact) == 9
            and artifact[0] == 'zkc.native-proof/0', 'expected native proof artifact')
    program = json.loads(artifact[4])
    require(len(program) == 5 and program[0] == 'zkc.program/0', 'expected executable program')
    bindings = {row[0]: row for row in program[1]}
    calls = Counter()

    def visit(node):
        if not isinstance(node, list):
            return
        if node and node[0] == 'op':
            require(len(node) == 6 and node[2] in bindings, 'unknown executable operation')
            calls[node[2]] += 1
        for child in node:
            visit(child)
    visit(program[2:4])
    return {'scope': 'static op sites in all emitted functions and participants; loops not expanded',
            'kernels': [{'binding': name, 'contract': row[1], 'arguments': row[2],
                         'implementation': row[3], 'call_sites': calls[name]}
                        for name, row in sorted(bindings.items())],
            'program_bytes': len(artifact[4].encode())}


def trace_summary(text):
    stages = [{'name': name, 'status': status, 'operations_before': int(before),
               'operations_after': int(after), 'microseconds': int(micros)}
              for name, status, before, after, micros in re.findall(
                  r'mathematical stage ([^:\n]+): (completed|refused), (\d+) -> (\d+) operations, (\d+) us', text)]
    decisions = [line.split('mathematical decision ', 1)[1] for line in text.splitlines()
                 if 'remark: mathematical decision ' in line]
    return {'stages': stages, 'decisions': decisions,
            'scope': 'separate preparation pass; not full package compilation',
            'aggregate_realization_work': None,
            'work_limit': 'CLI exposes stage counts and decision/capacity remarks, not aggregate allowances'}


def execution_metrics(report):
    execution = report.get('execution', {})
    missing = [key for key in COUNTERS if key not in execution]
    require(not missing, f'missing required execution counters: {missing}')
    require(all(type(execution[key]) is int and execution[key] >= 0 for key in COUNTERS),
            'invalid execution counter')
    require(execution.get('stop') is None and not execution.get('cleanup_errors'),
            'successful execution has a stop or cleanup error')
    return {**{key: execution[key] for key in COUNTERS},
            'exit_storage': {key: execution.get(key) for key in EXIT_COUNTERS},
            'exit_storage_unavailable': [key for key in EXIT_COUNTERS if key not in execution],
            'resources': execution.get('resources'), 'attempts': execution.get('attempts'),
            'capacity': report.get('capacity'), 'ring_work_limit': execution.get('ring_work_limit'),
            'external_work_limit': execution.get('external_work_limit')}


def observe_storage(case, policy, flags, inputs, directory, tools, journal):
    """Separate interactive observation: exit storage, not proof cost or peak RSS."""
    compiler, runtime, _ = tools
    module = case['entry'].split('::')[0]
    entry = f'{module}::Run'
    if case['entry'].endswith('::ProofProduct'):
        source = directory / 'storage.zkc'
        source.write_text((inputs / 'main.zkc').read_text() +
                          '\nrun Storage = MachineProof<GrandProduct<Extension>>;\n')
        flags = [f'--module={module}={source}' if x.startswith(f'--module={module}=') else x
                 for x in flags]
        entry = f'{module}::Storage'
    package = directory / 'storage.zkpkg'
    journal.command([compiler, 'language-package', '--source-format=zkc', f'--entry={entry}',
                     *flags, *POLICIES[policy]], cwd=directory, stdout=package)
    public = json.loads((inputs / 'public.json').read_text())
    witness = json.loads((inputs / 'witness.json').read_text())
    prover, verifier = directory / 'P.json', directory / 'V.json'
    write_json(prover, public | witness)
    write_json(verifier, public)
    outputs = directory / 'storage-outputs.json'
    report, command = journal.report([runtime, '--json', 'run', f'--package={package}',
        f'--sha256={digest(package)}', '--session=protocol-measurement-storage',
        f'--input=P={prover}', f'--input=V={verifier}', f'--results={outputs}'],
        cwd=directory, status='executed')
    require(json.loads(outputs.read_text())['roles']['V']['accepted'] is True,
            'interactive storage observation did not accept')
    execution = report['execution']
    roles = execution['roles']
    require(all('usage' in role and 'live_resource_units' in role and
                'retained_output_units' in role for role in roles),
            'interactive report missing exit storage counters')
    return {'scope': 'separate interactive Entry; per-role exit snapshot, not proof work or peak memory',
            'wall_seconds': command['wall_seconds'], 'package': identity(package),
            'roles': roles, 'backends': execution.get('backends'), 'capacity': report.get('capacity')}


def trial(case, variant, flags, inputs, directory, tools, timeout, interactive_storage=False):
    directory.mkdir(parents=True)
    journal = Journal(directory / 'commands', timeout)
    record = {'case': case['name'], 'variant': variant, 'status': 'failed'}
    try:
        compiler, runtime, opt = tools
        policy = variant.split('/', 1)[1]
        package_path = directory / 'entry.zkpkg'
        base = ['--source-format=zkc', f'--entry={case["entry"]}', *flags]
        compiled = journal.command([compiler, 'language-package', *base, *POLICIES[policy]],
                                   cwd=directory, stdout=package_path)
        record['compile_wall_seconds'] = compiled['wall_seconds']
        package = json.loads(package_path.read_text())
        require(package['format'] == 'zkc.entry/0', 'unexpected package format')
        require(package['options'] == {'simplify': True, 'finite_bulk': policy != 'no-finite-bulk',
                'release_storage': policy == 'release-storage', 'fuse_vector_reductions': False},
                'compiler did not apply requested policy')
        record['package'] = identity(package_path)
        record['original_inventory'] = logical_inventory(package['original'])
        record['emitted_inventory'] = kernel_inventory(package)

        original = directory / 'original.mlir'
        frontend = journal.command([compiler, 'language-emit', *base], cwd=directory, stdout=original)
        require(original.read_text() == package['original'], 'frontend IR differs from packaged original')
        record['frontend_emit_wall_seconds'] = frontend['wall_seconds']
        record['preparation'] = {'available': False, 'reason': 'no optimizer binary supplied'}
        if opt:
            prepared = directory / 'prepared.mlir'
            diagnostics = journal.command([opt, original, '--mlir-print-op-generic',
                '--mlir-print-op-on-diagnostic=false',
                '--mlir-print-stacktrace-on-diagnostic=false',
                '--zkc-prepare-protocol=trace-mathematics=true optimize-finite=' +
                str(policy != 'no-finite-bulk').lower()], cwd=directory, stdout=prepared)
            trace = trace_summary(Path(diagnostics['stderr']).read_text())
            require(trace['stages'], 'optimizer emitted no mathematical stage measurements')
            record['preparation'] = {'available': True, 'wall_seconds': diagnostics['wall_seconds'],
                                     **trace, 'inventory': logical_inventory(prepared.read_text())}

        proof = directory / 'proof.bin'
        native = [runtime, '--json']
        arguments = [f'--package={package_path}', f'--sha256={record["package"]["sha256"]}',
                     f'--public={inputs / "public.json"}']
        produced, proving = journal.report([*native, 'prove', *arguments,
            f'--witness={inputs / "witness.json"}', f'--output={proof}'], cwd=directory, status='produced')
        record['prove'] = execution_metrics(produced) | {'wall_seconds': proving['wall_seconds']}
        verified, verifying = journal.report([*native, 'verify', *arguments, f'--proof={proof}'],
                                             cwd=directory, status='accepted')
        record['verify'] = execution_metrics(verified) | {'wall_seconds': verifying['wall_seconds']}
        record['proof'] = identity(proof)
        require(produced.get('proof_sha256') == record['proof']['sha256'], 'proof digest differs from report')

        # A well-formed proof for a different public statement must be rejected.
        public = json.loads((inputs / 'public.json').read_text())
        public['query_count'] = str(int(public['query_count']) + 1)
        changed_public = directory / 'changed-public.json'
        write_json(changed_public, public)
        rejected, _ = journal.report([*native, 'verify', *arguments[:2],
            f'--public={changed_public}', f'--proof={proof}'], cwd=directory, status='refused', refused=True)
        require(rejected.get('phase') == 'execution', 'negative control failed before execution')
        record['changed_public_refusal'] = {'code': rejected.get('code'), 'phase': rejected.get('phase')}
        if interactive_storage:
            record['interactive_storage'] = observe_storage(case, policy, flags, inputs,
                                                            directory, tools, journal)
        record['status'] = 'passed'
    except (MeasurementError, OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        record['error'] = f'{type(error).__name__}: {error}'
    finally:
        write_json(directory / 'result.json', record)
    return record


def summaries(results):
    groups = defaultdict(list)
    for result in results:
        groups[(result['case'], result['variant'])].append(result)
    summary = []
    for (case, variant), values in sorted(groups.items()):
        passed = [v for v in values if v['status'] == 'passed']
        item = {'case': case, 'variant': variant, 'passed': len(passed), 'total': len(values)}
        # Failed cells retain raw partial work, but never contribute favorable timings.
        if len(passed) == len(values):
            metrics = {'compile_wall_seconds': [v['compile_wall_seconds'] for v in passed],
                       'frontend_emit_wall_seconds': [v['frontend_emit_wall_seconds'] for v in passed],
                       'package_bytes': [v['package']['bytes'] for v in passed],
                       'proof_bytes': [v['proof']['bytes'] for v in passed]}
            for phase in ('prove', 'verify'):
                for key in ('wall_seconds', *COUNTERS):
                    metrics[f'{phase}.{key}'] = [v[phase][key] for v in passed]
            item['metrics'] = {k: {'min': min(v), 'median': statistics.median(v), 'max': max(v)}
                               for k, v in metrics.items()}
        summary.append(item)
    return summary


def write_summary_csv(path, groups, status):
    """Side-by-side cells for comparison; raw samples remain authoritative."""
    fields = ['run_status', 'case', 'variant', 'passed', 'total', 'metric', 'min', 'median', 'max']
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for group in groups:
            cell = {'run_status': status} | {key: group[key] for key in fields[1:5]}
            for metric, statistics in group.get('metrics', {'unavailable': {}}).items():
                writer.writerow(cell | {'metric': metric} | statistics)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-source', required=True, type=Path)
    parser.add_argument('--baseline-revision', required=True)
    parser.add_argument('--current-source', type=Path)
    for source in ('baseline', 'current'):
        for tool in ('compiler', 'runtime', 'opt'):
            parser.add_argument(f'--{source}-{tool}', type=executable)
    parser.add_argument('--baseline-only', action='store_true', help='prototype only the baseline')
    parser.add_argument('--output', required=True, type=Path, help='new, exclusive result directory')
    parser.add_argument('--case', action='append', choices=[c['name'] for c in case_catalog()])
    parser.add_argument('--repetitions', type=positive_integer, default=3)
    parser.add_argument('--timeout', type=positive_timeout, default=300)
    parser.add_argument('--release-storage', action='store_true', help='add a separate current policy')
    parser.add_argument('--interactive-storage', action='store_true',
                        help='also observe per-role exit storage using a separate interactive Entry')
    args = parser.parse_args(argv)
    for source in ('baseline',) if args.baseline_only else ('baseline', 'current'):
        for part in ('source', 'compiler', 'runtime'):
            if getattr(args, f'{source}_{part}') is None:
                parser.error(f'--{source}-{part} is required')
    if args.baseline_only and (args.release_storage or any(
            getattr(args, f'current_{part}') for part in ('source', 'compiler', 'runtime', 'opt'))):
        parser.error('--baseline-only accepts no current tools/source or current policy')
    return args


def main(argv=None):
    args = parse_args(argv)
    output = args.output.expanduser().resolve()
    try:
        output.mkdir(parents=True, exist_ok=False)
    except FileExistsError:
        print(f'refusing to overwrite existing evidence: {output}', file=sys.stderr)
        return 2
    journal = Journal(output / 'setup', args.timeout)
    cases = [c for c in case_catalog() if not args.case or c['name'] in args.case]
    labels = ['baseline'] if args.baseline_only else ['baseline', 'current']
    result = {'format': FORMAT, 'status': 'failed', 'argv': sys.argv if argv is None else argv,
              'host': {'platform': platform.platform(), 'python': sys.version,
                       'cpu_count': os.cpu_count(), 'machine': platform.machine()},
              'repetitions': args.repetitions, 'warmup_runs': 0,
              'order': 'serial; rotate variant order by repetition; diagnostics separate',
              'sources': {}, 'tools': {}, 'cases': cases, 'results': []}
    try:
        result['tool_source'] = identity(Path(__file__).resolve())
        shutil.copyfile(__file__, output / 'protocol_math.py')
        shutil.copyfile(ROOT / 'scripts/processes.py', output / 'processes.py')
        shutil.copytree(Path(__file__).parent / 'bench', output / 'bench',
                        ignore=shutil.ignore_patterns('__pycache__'))
        result['process_helper'] = identity(ROOT / 'scripts/processes.py')
        cpuinfo = Path('/proc/cpuinfo')
        if cpuinfo.is_file():
            result['host']['cpu_model'] = next((line.split(':', 1)[1].strip()
                for line in cpuinfo.read_text().splitlines() if line.startswith('model name')), None)
        roots, binaries, prepared = {}, {}, {}
        for label in labels:
            root = getattr(args, f'{label}_source').expanduser().resolve()
            frozen = output / 'sources' / label
            result['sources'][label] = snapshot(root, frozen, cases, journal,
                args.baseline_revision if label == 'baseline' else None)
            roots[label] = root
            binaries[label] = tuple(getattr(args, f'{label}_{tool}') for tool in ('compiler', 'runtime', 'opt'))
            result['tools'][label] = {name: identity(path) if path else None
                for name, path in zip(('compiler', 'runtime', 'opt'), binaries[label])}
            for case in cases:
                inputs = output / 'cases' / case['name'] / label
                prepared[label, case['name']] = (prepare_case(frozen, case, inputs, journal), inputs)
        for case in cases:
            for name in ('public', 'witness'):
                baseline = json.loads((prepared['baseline', case['name']][1] / f'{name}.json').read_text())
                if 'current' in labels:
                    current = json.loads((prepared['current', case['name']][1] / f'{name}.json').read_text())
                    require(current == baseline, f'{case["name"]}: baseline/current {name} inputs differ')
        variants = [('baseline', 'default')]
        if 'current' in labels:
            variants += [('current', 'default'), ('current', 'no-finite-bulk')]
            if args.release_storage:
                variants.append(('current', 'release-storage'))
        write_json(output / 'manifest.json', result)
        for repetition in range(args.repetitions):
            order = variants[repetition % len(variants):] + variants[:repetition % len(variants)]
            for case in cases:
                for label, policy in order:
                    print(f'{case["name"]} {label}/{policy} repetition {repetition+1}', flush=True)
                    flags, inputs = prepared[label, case['name']]
                    directory = output / 'runs' / case['name'] / label / policy / f'{repetition+1:03d}'
                    measured = trial(case, f'{label}/{policy}', flags, inputs, directory,
                                     binaries[label], args.timeout, args.interactive_storage)
                    result['results'].append(measured | {'repetition': repetition + 1})
                    write_json(output / 'manifest.json', result)
        # A concurrently edited original or replaced binary invalidates this comparison.
        for label in labels:
            for relative, expected in result['sources'][label]['files'].items():
                require(digest(roots[label] / relative) == expected,
                        f'source changed during measurement: {label}/{relative}')
            for tool in result['tools'][label].values():
                if tool:
                    require(digest(Path(tool['path'])) == tool['sha256'],
                            f'binary changed during measurement: {tool["path"]}')
        result['status'] = 'passed' if all(r['status'] == 'passed' for r in result['results']) else 'failed'
    except (MeasurementError, OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        result['error'] = f'{type(error).__name__}: {error}'
    except KeyboardInterrupt:
        result['status'] = 'interrupted'
    finally:
        result['summary'] = summaries(result['results'])
        write_json(output / 'manifest.json', result)
        write_json(output / 'summary.json', {'format': FORMAT, 'status': result['status'],
                                            'groups': result['summary']})
        write_summary_csv(output / 'summary.csv', result['summary'], result['status'])
    print(f'{result["status"]}: {output / "manifest.json"}', flush=True)
    return 0 if result['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
