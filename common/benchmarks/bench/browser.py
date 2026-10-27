"""Prepared ProofClient cases using the common capture, journal and report owners."""
import gzip
import json
import math
from pathlib import Path
import shutil
import sys

from .io import Journal, ROOT, digest, measurement_slot, read_report, require, write_json
from .runner import Capture, host_info
from .results import FORMAT, distribution

CASE_FORMAT = 'zkc.browser-cases/0'
PROVIDERS = {'arkworks', 'blst', 'dalek', 'halo2curves', 'plonky3'}
BOUNDARIES = {
    'fetch_ms': 'Wasm HTTP fetch and arrayBuffer in the page; local server, no compression',
    'compile_ms': 'WebAssembly.compile of resident bytes; engine cache may be warm',
    'glue_initialize_ms': 'binding initialization with compiled Module, includes instantiate',
    'instantiate_api_ms': 'await WebAssembly.instantiate(Module, imports), inside glue_initialize_ms',
    'worker_ready_ms': 'ProofClient construction through ready with compiled Module; includes fresh instance/glue and Worker startup',
    'admit_roundtrip_ms': 'ProofClient.admit; snapshot/transport, capture, authority decoding, admission and reply',
    'package_capture_ms': 'Package::capture only, within admit_roundtrip_ms; optional SDK observation',
    'package_admit_ms': 'ProofEntry admission only, within admit_roundtrip_ms; excludes capture and constructor policy/authority decoding',
    'memory_preflight_ms': 'bounded common document decoding, codec feasibility and output-key preflight; excludes Host invocation preparation; within worker_call_ms',
    'execute_cleanup_ms': 'Host preparation, input-key imports, reconstruction, execution and cleanup; within worker_call_ms',
    'output_encode_ms': 'SDK result encoding; within worker_call_ms',
    'diagnostics_ms': 'SDK diagnostic materialization; excludes report JSON serialization; within worker_call_ms',
    'setup_roundtrip_ms': 'setSetup; snapshot/transport and byte installation, not semantic key import',
    'end_to_end_ms': 'client call through reply; includes snapshot/queue, transfer, SDK call, getter copies and publication/delivery',
    'worker_call_ms': 'synchronous Wasm facade including ABI input conversion, SDK decode/setup/preflight, execution/cleanup, encoding and report construction; excludes result getters',
    'outside_worker_call_ms': 'end_to_end_ms minus worker_call_ms, inclusive residual; not isolated transfer',
    'transfer_probe_ms': 'dedicated MessageChannel transferable roundtrip including scheduling; separate calibration, not proof transport',
}
UNAVAILABLE = ['document_decode_without_preflight', 'semantic_material_import_without_execution',
               'host_preparation_without_execution',
               'js_wasm_copy', 'result_getters', 'publication_delivery']


def milliseconds(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def artifact(path, capture, relative):
    record = capture.add(path, relative)
    return record | {'gzip_level': 9, 'gzip_bytes': len(gzip.compress(Path(path).read_bytes(), mtime=0))}


def prepare_cases(path, output, capture):
    """Capture candidate files; the supplied pin remains an independent input."""
    document = json.loads(path.read_text())
    require(isinstance(document, dict) and set(document) == {'format', 'cases'}
            and document['format'] == CASE_FORMAT, 'invalid browser cases document')
    require(isinstance(document['cases'], list) and document['cases'], 'empty browser cases')
    capture.add(path, 'browser-cases.json')
    cases, names = [], set()
    for candidate in document['cases']:
        require(isinstance(candidate, dict) and {'name', 'directory', 'providers'} <= candidate.keys()
                and not candidate.keys() - {'name', 'directory', 'providers', 'options', 'statements', 'authority', 'setups', 'expected_outputs', 'bindings'},
                'invalid browser case fields')
        name = candidate['name']
        require(isinstance(name, str) and name and len(name) <= 128
                and all(c.isascii() and (c.isalnum() or c in '-_') for c in name)
                and name not in names, 'invalid or duplicate browser case name')
        names.add(name)
        providers = candidate['providers']
        require(isinstance(providers, list) and all(isinstance(p, str) and p in PROVIDERS for p in providers)
                and len(set(providers)) == len(providers), 'invalid browser providers')
        require(isinstance(candidate['directory'], str), 'invalid fixture directory')
        directory = (path.parent / candidate['directory']).resolve()
        target = output / 'fixtures' / name
        target.mkdir(parents=True)
        files = {}
        def copy(filename, logical):
            require(isinstance(filename, str) and filename, 'invalid fixture file')
            source = (directory / filename).resolve()
            destination = target / logical
            record = artifact(source, capture, Path('fixtures') / name / logical)
            shutil.copyfile(capture.directory / 'fixtures' / name / logical, destination)
            require(digest(destination) == record['sha256'], 'fixture changed during preparation')
            capture.add(destination)
            files[logical] = record
            return str(destination)
        package = copy('entry.zkpkg', 'entry.zkpkg')
        pin_path = copy('pin.txt', 'pin.txt')
        pin = Path(pin_path).read_text().strip()
        require(len(pin) == 64 and all(c in '0123456789abcdef' for c in pin), 'invalid browser package pin')
        require(digest(Path(package)) == pin, 'browser candidate does not match supplied package pin')
        options = candidate.get('options', {})
        require(isinstance(options, dict) and 'providers' not in options, 'providers must be supplied once')
        statements = candidate.get('statements', [{'public': 'public.json', 'witness': 'witness.json'}])
        require(isinstance(statements, list) and statements, 'empty browser statement schedule')
        inputs = []
        for i, statement in enumerate(statements):
            require(isinstance(statement, dict) and set(statement) == {'public', 'witness'}, 'invalid browser statement')
            inputs.append({key: copy(statement[key], f'{i}-{key}.json') for key in ('public', 'witness')})
        setups = []
        for i, setup in enumerate(candidate.get('setups', [])):
            require(isinstance(setup, dict) and set(setup) == {'slot', 'path'} and isinstance(setup['slot'], str)
                    and setup['slot'], 'invalid browser setup')
            require(setup['slot'] not in {s['slot'] for s in setups}, 'duplicate browser setup slot')
            setups.append({'slot': setup['slot'], 'path': copy(setup['path'], f'{i}-setup.bin')})
        bindings = []
        for i, binding in enumerate(candidate.get('bindings', [])):
            require(isinstance(binding, dict) and set(binding) == {'name', 'path'}
                    and isinstance(binding['name'], str) and binding['name']
                    and binding['name'] not in {b['name'] for b in bindings}, 'invalid browser binding')
            bindings.append({'name': binding['name'], 'path': copy(binding['path'], f'{i}-binding.bin')})
        authority = copy(candidate['authority'], 'authority.json') if 'authority' in candidate else None
        expected = copy(candidate['expected_outputs'], 'expected-outputs.json') if 'expected_outputs' in candidate else None
        if expected:
            require(isinstance(json.loads(Path(expected).read_text()), dict), 'expected outputs must be an object')
        bindings_used = []
        def find_program(value):
            if isinstance(value, list):
                if value and value[0] == 'zkc.program/0':
                    bindings_used.extend(value[1])
                else:
                    for child in value:
                        find_program(child)
            elif isinstance(value, str) and value.startswith('['):
                try:
                    find_program(json.loads(value))
                except ValueError:
                    pass
        package_document = json.loads(Path(package).read_text())
        find_program(package_document['artifact'])
        cases.append({'name': name, 'directory': str(target), 'package': package, 'pin': pin,
                      'options': options | {'providers': sorted(providers)}, 'inputs': inputs,
                      'physical_bindings': bindings_used,
                      'setups': setups, 'bindings': bindings, 'authority': authority, 'expected_outputs': expected, 'files': files})
    return cases


def validate_observation(report, cases, variants, plan):
    require(isinstance(plan, dict) and set(plan) == {'warmups', 'samples'}
            and type(plan['warmups']) is int and plan['warmups'] >= 0
            and type(plan['samples']) is int and plan['samples'] > 0, 'invalid browser plan')
    require(isinstance(variants, list) and variants and len(set(variants)) == len(variants)
            and all(v in ('portable', 'simd') for v in variants), 'invalid browser variants')
    require(isinstance(report, dict) and report.get('format') == 'zkc.browser-worker/0'
            and report.get('status') == 'passed', 'browser measurement failed')
    require(report.get('variants') == variants, 'browser variants differ')
    modules = report.get('modules')
    require(isinstance(modules, list) and [m.get('variant') for m in modules] == variants, 'incomplete browser modules')
    for module in modules:
        require(type(module.get('bytes')) is int and module['bytes'] > 0, 'invalid module bytes')
        for field in ('fetch_ms', 'compile_ms', 'glue_initialize_ms'):
            require(milliseconds(module.get(field)), f'invalid module {field}')
        require(module.get('instantiate_api_ms') is None or milliseconds(module['instantiate_api_ms']), 'invalid instantiate timing')
    rows = report.get('cases')
    require(isinstance(rows, list) and len(rows) == len(cases) * len(variants), 'incomplete browser matrix')
    wanted = {(c['name'], v): c for c in cases for v in variants}
    seen = set()
    for row in rows:
        key = (row.get('name'), row.get('variant'))
        require(key in wanted and key not in seen, 'unknown or duplicate browser result')
        seen.add(key)
        case = wanted[key]
        require(row.get('pin') == case['pin'] and row.get('providers') == case['options']['providers'], 'browser support or package differs')
        require(milliseconds(row.get('admit_roundtrip_ms')) and milliseconds(row.get('worker_ready_ms')), 'invalid browser startup timing')
        for field, value in (row.get('sdk_admission_ms') or {}).items():
            require(field in ('package_capture_ms', 'package_admit_ms') and milliseconds(value), 'invalid SDK admission timing')
        calls = row.get('calls')
        require(isinstance(calls, list) and len(calls) == (plan['samples'] + plan['warmups']) * len(case['inputs']) * 2,
                'incomplete browser call schedule')
        for index, call in enumerate(calls):
            operation = ('prove', 'verify')[index % 2]
            statement = index // 2 % len(case['inputs'])
            cycle = index // (2 * len(case['inputs']))
            require(call.get('operation') == operation and call.get('input_index') == statement
                    and call.get('cycle') == cycle
                    and call.get('phase') == ('warmup' if cycle < plan['warmups'] else 'sample'), 'browser call order differs')
            require(call.get('success') is True and (operation != 'verify' or call.get('accepted') is True), 'browser call refused')
            for field in ('end_to_end_ms', 'worker_call_ms', 'outside_worker_call_ms'):
                require(milliseconds(call.get(field)), f'invalid browser {field}')
            require(abs(call['end_to_end_ms'] - call['worker_call_ms'] - call['outside_worker_call_ms']) < 0.001,
                    'browser residual timing differs')
            for field, value in (call.get('sdk_phases_ms') or {}).items():
                require(field in ('memory_preflight_ms', 'execute_cleanup_ms', 'output_encode_ms', 'diagnostics_ms') and milliseconds(value), 'invalid SDK call timing')
            require(isinstance(call.get('outputs_sha256'), str) and len(call['outputs_sha256']) == 64, 'missing browser output identity')
        require(row.get('checks', {}).get('outputs_match') is True, 'browser output check missing')
        if len(variants) > 1:
            require(row['checks'].get('cross_variant_verified') is True, 'browser variant cross-verification missing')



def validate_native(report, cases, variants, required):
    if not required:
        return
    wanted = {(case['name'], variant, i) for case in cases for variant in variants for i in range(len(case['inputs']))}
    rows = report.get('native')
    require(isinstance(rows, list) and len(rows) == len(wanted), 'incomplete native browser cross-verification')
    seen = set()
    for row in rows:
        key = (row.get('name'), row.get('variant'), row.get('input_index'))
        require(key in wanted and key not in seen and row.get('cross_verified') is True, 'invalid native cross-verification')
        seen.add(key)

def run(args):
    with measurement_slot(args.output.resolve() / 'coordination.json', exclusive=args.exclusive):
        output = args.output.resolve()
        output.mkdir(parents=True)
        capture = Capture(output / 'capture')
        manifest = {'format': FORMAT, 'observation': 'browser', 'status': 'running', 'phase': 'preparation',
                    'plan': {'warmups': args.warmups, 'samples': args.samples}, 'processes': args.processes,
                    'argv': sys.argv, 'label': args.label, 'transport': args.transport, 'native_cross_verification': args.native_example is not None, 'source': {'revision': args.revision, 'scope': 'caller supplied; captured files identify consumed artifacts'},
                    'host': host_info(), 'files': capture.files, 'results': [], 'cases': [],
                    'variants': args.variant or ['portable'], 'boundaries': BOUNDARIES,
                    'unavailable_phases': UNAVAILABLE, 'artifacts': {}}
        try:
            require(len(set(manifest['variants'])) == len(manifest['variants']), 'duplicate browser variant')
            web = args.web.resolve()
            deployed = output / 'web'
            deployed.mkdir()
            for path in sorted(web.iterdir()):
                if path.is_file() and path.suffix in ('.mjs', '.js', '.html'):
                    capture.add(path, Path('web') / path.name)
                    shutil.copyfile(capture.directory / 'web' / path.name, deployed / path.name)
                    capture.add(deployed / path.name)
            for variant in manifest['variants']:
                folder = 'pkg-simd' if variant == 'simd' else 'pkg'
                (deployed / folder).mkdir()
                manifest['artifacts'][variant] = {}
                for filename in ('zkc_web.js', 'zkc_web_bg.wasm'):
                    path = web / folder / filename
                    manifest['artifacts'][variant][filename] = artifact(path, capture, Path('web') / folder / filename)
                    shutil.copyfile(capture.directory / 'web' / folder / filename, deployed / folder / filename)
                    capture.add(deployed / folder / filename)
            manifest['cases'] = prepare_cases(args.cases.resolve(), output, capture)
            for path in sorted((ROOT / 'common/benchmarks').rglob('*')):
                if path.is_file() and path.suffix in ('.py', '.mjs'):
                    capture.add(path, Path('measurement') / path.relative_to(ROOT))
            capture.add(args.node)
            capture.add(args.playwright)
            capture.add(args.playwright.parent / 'package.json')
            if args.native_example:
                capture.add(args.native_example)
            request = {'web': str(deployed), 'cases': manifest['cases'], 'variants': manifest['variants'],
                       'plan': manifest['plan'], 'playwright': str(args.playwright.resolve()),
                       'native_example': str(args.native_example) if args.native_example else None,
                       'timeout_ms': args.timeout * 1000, 'transport': args.transport, 'output': str(output)}
            request_path = output / 'request.json'
            write_json(request_path, request)
            manifest['phase'] = 'measurement'
            write_json(output / 'manifest.json', manifest)
            for repetition in range(args.processes):
                record = Journal(output / 'runs' / str(repetition), args.timeout).command(
                    [args.node, ROOT / 'common/benchmarks/bench/browser.mjs', request_path, str(repetition)], cwd=ROOT)
                report = read_report(record)
                validate_observation(report, manifest['cases'], manifest['variants'], manifest['plan'])
                require(report['transport'] == args.transport, 'browser transport differs')
                validate_native(report, manifest['cases'], manifest['variants'], args.native_example is not None)
                for proof in report.get('proofs', []):
                    path = Path(proof['path']).resolve()
                    require(path.is_relative_to(output / 'proofs' / str(repetition)), 'browser proof escaped output')
                    proof_record = capture.add(path)
                    require(proof_record['sha256'] == proof['sha256'] and proof_record['bytes'] == proof['bytes'], 'browser proof identity differs')
                manifest['results'].append({'repetition': repetition, 'worker': report, 'process_wall_seconds': record['wall_seconds']})
                write_json(output / 'manifest.json', manifest)
            capture.check()
            manifest['phase'], manifest['status'] = 'complete', 'passed'
        except Exception as error:
            manifest['status'], manifest['error'] = 'failed', f'{type(error).__name__}: {error}'
        except KeyboardInterrupt:
            manifest['status'] = 'interrupted'
        finally:
            publish(output, manifest)
        print(f"{manifest['status']}: {output / 'manifest.json'}", flush=True)
        return 0 if manifest['status'] == 'passed' else 1


def validate_manifest(manifest):
    require(not (manifest.keys() - {'format', 'observation', 'status', 'phase', 'plan', 'processes', 'label',
            'source', 'host', 'files', 'results', 'cases', 'variants', 'boundaries', 'unavailable_phases', 'artifacts', 'error', 'transport', 'native_cross_verification', 'argv'}),
            'unknown browser manifest fields')
    require(manifest.get('format') == FORMAT and manifest.get('observation') == 'browser', 'invalid browser manifest')
    require(manifest.get('status') in ('running', 'passed', 'failed', 'interrupted'), 'invalid browser status')
    require(isinstance(manifest.get('results'), list), 'invalid browser results')
    if manifest['status'] != 'passed':
        return
    require(type(manifest.get('processes')) is int and manifest['processes'] > 0
            and len(manifest['results']) == manifest['processes'], 'incomplete browser processes')
    require({r['repetition'] for r in manifest['results']} == set(range(manifest['processes'])), 'duplicate browser process')
    for result in manifest['results']:
        validate_observation(result['worker'], manifest['cases'], manifest['variants'], manifest['plan'])
        if manifest.get('native_cross_verification'):
            validate_native(result['worker'], manifest['cases'], manifest['variants'], True)


def publish(directory, manifest):
    validate_manifest(manifest)
    rows, modules, transfer_probes = [], [], []
    if manifest['status'] == 'passed':
        for variant in manifest['variants']:
            observations = [next(m for m in r['worker']['modules'] if m['variant'] == variant) for r in manifest['results']]
            module = {'variant': variant, 'bytes': observations[0]['bytes']}
            for field in ('fetch_ms', 'compile_ms', 'glue_initialize_ms', 'instantiate_api_ms'):
                values = [m.get(field) for m in observations]
                module[field] = distribution(values) if all(milliseconds(v) for v in values) else None
            modules.append(module)
        for size in (0, 32768, 1048576):
            observations = [next((p['roundtrip_ms'] for p in r['worker'].get('transfer_probes', []) if p['bytes'] == size), None)
                            for r in manifest['results']]
            if all(observations):
                transfer_probes.append({'bytes': size, 'roundtrip_ms': distribution([distribution(v)['median'] for v in observations])})
        for case in manifest['cases']:
            for variant in manifest['variants']:
                measured = [row for r in manifest['results'] for row in r['worker']['cases']
                            if row['name'] == case['name'] and row['variant'] == variant]
                for operation in ('prove', 'verify'):
                    row = {'case': case['name'], 'variant': variant, 'operation': operation}
                    for field in ('worker_ready_ms', 'admit_roundtrip_ms'):
                        row[field] = distribution([r[field] for r in measured])
                    row['setup_roundtrip_ms'] = {setup['slot']: distribution([next(s['milliseconds'] for s in r['setup_roundtrip_ms']
                        if s['slot'] == setup['slot']) for r in measured]) for setup in case.get('setups', [])}
                    for field in ('end_to_end_ms', 'worker_call_ms', 'outside_worker_call_ms'):
                        values = [[c[field] for c in r['calls'] if c['operation'] == operation and c['phase'] == 'sample'] for r in measured]
                        row[field] = distribution([distribution(v)['median'] for v in values])
                        row['first_' + field] = distribution([next(c[field] for c in r['calls'] if c['operation'] == operation) for r in measured])
                    row['sdk_phases_ms'] = {}
                    row['first_sdk_phases_ms'] = {}
                    for field in ('memory_preflight_ms', 'execute_cleanup_ms', 'output_encode_ms', 'diagnostics_ms'):
                        groups = [[c.get('sdk_phases_ms', {}).get(field) if c.get('sdk_phases_ms') else None
                                   for c in r['calls'] if c['operation'] == operation and c['phase'] == 'sample'] for r in measured]
                        row['sdk_phases_ms'][field] = (distribution([distribution(v)['median'] for v in groups])
                            if all(milliseconds(v) for group in groups for v in group) else None)
                        first = [next(c for c in r['calls'] if c['operation'] == operation).get('sdk_phases_ms') for r in measured]
                        row['first_sdk_phases_ms'][field] = (distribution([v[field] for v in first])
                            if all(v and milliseconds(v.get(field)) for v in first) else None)
                    row['sdk_admission_ms'] = {field: distribution([r['sdk_admission_ms'][field] for r in measured])
                        if all(r.get('sdk_admission_ms') and milliseconds(r['sdk_admission_ms'].get(field)) for r in measured) else None
                        for field in ('package_capture_ms', 'package_admit_ms')}
                    rows.append(row)
    write_json(directory / 'manifest.json', manifest)
    write_json(directory / 'summary.json', {'format': FORMAT, 'observation': 'browser', 'status': manifest['status'], 'rows': rows,
                                          'modules': modules, 'artifacts': manifest.get('artifacts', {}), 'transfer_probes': transfer_probes,
                                          'boundaries': BOUNDARIES, 'unavailable_phases': UNAVAILABLE})
    lines = ['# Browser measurements', '', f"Status: **{manifest['status']}**. Exploratory unless a quiet interval was arranged.", '',
             'Times are medians of process medians. First calls include the first warmup. Intervals overlap; do not add them.', '',
             'Small stages can be below the observed page timer increment recorded in manifest.json.', '',
             '| Module | Raw bytes | Gzip bytes | Fetch ms | Compile ms | Glue initialize ms | Nested instantiate ms |',
             '|---|---:|---:|---:|---:|---:|---:|']
    for module in modules:
        artifact = manifest.get('artifacts', {}).get(module['variant'], {}).get('zkc_web_bg.wasm', {})
        values = [module[field] for field in ('fetch_ms', 'compile_ms', 'glue_initialize_ms', 'instantiate_api_ms')]
        lines.append(f"| {module['variant']} | {module['bytes']} | {artifact.get('gzip_bytes', 'unavailable')} | "
                     + ' | '.join(f"{v['median']:.6f}" if v else 'unavailable' for v in values) + ' |')
    lines += ['', '| Case | Variant | Worker ready ms | Admission roundtrip ms | Setup byte installation ms |',
              '|---|---|---:|---:|---|']
    for row in rows:
        if row['operation'] == 'prove':
            setups = ', '.join(f"{slot}: {value['median']:.6f}" for slot, value in row['setup_roundtrip_ms'].items()) or 'none'
            lines.append(f"| {row['case']} | {row['variant']} | {row['worker_ready_ms']['median']:.6f} | {row['admit_roundtrip_ms']['median']:.6f} | {setups} |")
    lines += ['',
             '| Case | Variant | Operation | First client ms | Repeated client ms | Repeated inclusive Wasm call ms |',
             '|---|---|---|---:|---:|---:|']
    for row in rows:
        lines.append(f"| {row['case']} | {row['variant']} | {row['operation']} | {row['first_end_to_end_ms']['median']:.6f} | {row['end_to_end_ms']['median']:.6f} | {row['worker_call_ms']['median']:.6f} |")
    lines += ['', '| Case | Variant | Operation | Document/output preflight ms | Prepare/execute/cleanup ms | Encode ms | Diagnostics ms |',
              '|---|---|---|---:|---:|---:|---:|']
    for row in rows:
        values = [row['sdk_phases_ms'][field] for field in ('memory_preflight_ms', 'execute_cleanup_ms', 'output_encode_ms', 'diagnostics_ms')]
        lines.append(f"| {row['case']} | {row['variant']} | {row['operation']} | " + ' | '.join(f"{v['median']:.6f}" if v else 'unavailable' for v in values) + ' |')
    lines += ['', 'Timing boundaries:', ''] + [f'- `{key}`: {value}.' for key, value in BOUNDARIES.items()]
    lines += ['', 'Exact unavailable phases: ' + ', '.join(UNAVAILABLE) + '.', '',
              'Raw/compressed artifact sizes, module observations, transport probes, per-call outputs and cross-verification receipts are in manifest.json.',
              'Module compilation may use engine code caches. Fresh Workers reset mutable state, not browser code caches.',
              'No total browser/Wasm heap, security or constant-time conclusion follows from these measurements.']
    if 'error' in manifest:
        lines += ['', manifest['error']]
    (directory / 'report.md').write_text('\n'.join(lines) + '\n')
