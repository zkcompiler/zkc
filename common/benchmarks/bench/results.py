"""Validate worker evidence and summarize independent process repetitions."""
from collections import defaultdict
import csv
import math
import statistics

from .io import require, write_json
from .observations import validate_counts, summarize_counts

FORMAT = 'zkc.benchmark/0'


def validate_preparation(stats, limits=None, previous_hits=0):
    require(isinstance(stats, dict) and set(stats) == {'entries', 'retained_bytes', 'hits'}
            and all(type(v) is int and v >= 0 for v in stats.values()), 'invalid preparation statistics')
    require(stats['hits'] >= previous_hits, 'preparation hits moved backwards')
    if limits is not None:
        require(stats['entries'] <= limits['entries'] and stats['retained_bytes'] <= limits['bytes'],
                'preparation exceeded its resource contract')
        if limits['entries'] == 0 or limits['bytes'] == 0:
            require(all(value == 0 for value in stats.values()), 'disabled preparation retained state')


def validate_preparation_limits(limits, request=None):
    require(isinstance(limits, dict) and set(limits) == {'entries', 'bytes', 'default_entries', 'default_bytes'}
            and all(type(v) is int and v >= 0 for v in limits.values()), 'invalid preparation limits')
    if request is None:
        return
    require(isinstance(request, dict) and request.get('kind') == 'host'
            and type(request.get('preparation')) is bool, 'missing preparation request')
    expected = []
    for name in ('entries', 'bytes'):
        value = request.get(f'preparation_{name}')
        require(value is None or type(value) is int and value >= 0, 'invalid requested preparation limit')
        expected.append((limits[f'default_{name}'] if value is None else value) if request['preparation'] else 0)
    require((limits['entries'], limits['bytes']) == tuple(expected), 'preparation limits differ from the request')


def validate_worker(report, plan, boundary):
    require(isinstance(report, dict), 'worker report must be an object')
    require(set(report) == {'format', 'status', 'boundary', 'samples', 'proof_bytes', 'admission_ns',
                           'process_peak_rss_bytes', 'proofs', 'build', 'process', 'timer_floor_ns', 'diagnostics', 'lifecycle'},
            'unexpected worker report fields')
    require(report.get('format') == 'zkc.benchmark-worker/0'
            and report.get('status') == 'passed', 'worker did not pass')
    require(report.get('boundary') == boundary, 'worker timing boundary changed')
    values = report.get('samples')
    require(isinstance(values, list) and len(values) == plan['samples'] + plan['warmups'],
            'incomplete worker samples')
    for i, sample in enumerate(values):
        require(isinstance(sample, dict), 'worker sample must be an object')
        require(set(sample) == {'index', 'iterations', 'phase', 'elapsed_ns', 'cpu_ns', 'first_call_ns'},
                'unexpected worker sample fields')
        require(type(sample.get('index')) is int and sample['index'] == i
                and type(sample.get('iterations')) is int and sample['iterations'] == plan['iterations']
                and sample.get('phase') == ('warmup' if i < plan['warmups'] else 'sample'),
                'worker sample plan mismatch')
        for name in ('elapsed_ns', 'cpu_ns', 'first_call_ns'):
            elapsed = sample.get(name)
            require(type(elapsed) is int and elapsed > 0, f'invalid worker time: {name}')
        require(sample['first_call_ns'] <= sample['elapsed_ns'], 'first call exceeds sample')
    for name in ('proof_bytes', 'admission_ns', 'process_peak_rss_bytes'):
        value = report.get(name)
        require((name != 'proof_bytes' and value is None) or (type(value) is int and value >= 0),
                f'invalid {name}')
    require(isinstance(report.get('proofs'), list), 'worker proofs must be an array')
    require(isinstance(report.get('process'), dict), 'worker process facts must be an object')
    build = report.get('build')
    require(isinstance(build, dict), 'worker build facts must be an object')
    require(build.get('optimized') is True or ('optimized' not in build
            and build.get('opt_level') in ('1', '2', '3', 's', 'z')),
            'benchmark worker must be built with optimization')
    require(build.get('debug_assertions') is False, 'benchmark worker must disable debug assertions')
    counted = build.get('execution_counts', False)
    require(type(counted) is bool, 'invalid execution counts capability')
    if boundary in ('admitted_entry_call', 'admitted_run_call'):
        require('execution_counts' in build, 'missing runtime observation capability')
    require(not counted or boundary in ('admitted_entry_call', 'admitted_run_call'),
            'execution counts require a source workload')
    lifecycle = report['lifecycle']
    if boundary in ('admitted_entry_call', 'admitted_run_call'):
        require(isinstance(lifecycle, dict), 'missing Host lifecycle measurements')
    if lifecycle is not None:
        require(isinstance(lifecycle, dict) and set(lifecycle) == {'capture_ns', 'admit_ns', 'calls',
                'diagnostics_ns', 'peak_rss_before_diagnostics', 'peak_rss_after_diagnostics', 'preparation_limits'}, 'invalid lifecycle fields')
        limits = lifecycle['preparation_limits']
        if boundary == 'admitted_entry_call':
            validate_preparation_limits(limits)
        else:
            require(limits is None, 'unexpected preparation limits')
        for name in ('capture_ns', 'admit_ns', 'diagnostics_ns'):
            require(type(lifecycle[name]) is int and lifecycle[name] >= 0, f'invalid lifecycle {name}')
        require(report['admission_ns'] == lifecycle['capture_ns'] + lifecycle['admit_ns'], 'admission boundary mismatch')
        for name in ('peak_rss_before_diagnostics', 'peak_rss_after_diagnostics'):
            require(lifecycle[name] is None or type(lifecycle[name]) is int and lifecycle[name] >= 0, f'invalid {name}')
        calls = lifecycle['calls']
        require(isinstance(calls, list) and len(calls) == len(values)*plan['iterations'], 'incomplete lifecycle calls')
        previous_hits = 0
        for call in calls:
            require(isinstance(call, dict) and {'input_index', 'decode_ns'} <= call.keys()
                    and not (call.keys() - {'input_index', 'decode_ns', 'preparation', 'execution_counts'}), 'invalid lifecycle call')
            require(type(call['input_index']) is int and call['input_index'] >= 0
                    and type(call['decode_ns']) is int and call['decode_ns'] >= 0, 'invalid lifecycle call values')
            if boundary == 'admitted_entry_call':
                require('preparation' in call, 'missing preparation statistics')
            if 'preparation' in call:
                stats = call['preparation']
                validate_preparation(stats, limits, previous_hits)
                previous_hits = stats['hits']
            require(('execution_counts' in call) == counted, 'call observation capability mismatch')
            if counted:
                validate_counts(call['execution_counts'])
        count = len({c['input_index'] for c in calls})
        require([c['input_index'] for c in calls] == [i % count for i in range(len(calls))], 'invalid lifecycle input order')
        if count > 1:
            require(plan['iterations'] == 1 and plan['warmups'] % count == 0 and plan['samples'] % count == 0,
                    'incomplete changing-input cycles')
    return report


def validate_manifest(manifest):
    """A successful saved run must contain the entire declared measurement matrix."""
    require(isinstance(manifest, dict) and manifest.get('format') == FORMAT, 'unknown benchmark format')
    require(not (set(manifest) - {'format', 'status', 'phase', 'results', 'contracts', 'plan', 'processes',
                'seed', 'label', 'argv', 'host', 'files', 'checks', 'matrix', 'schedule', 'compilation',
                'cli', 'source', 'harness', 'comparisons', 'threads', 'references', 'error', 'observation', 'compiler_options'}), 'unknown manifest fields')
    require(manifest.get('status') in ('passed', 'failed', 'interrupted', 'running'), 'unknown benchmark status')
    require(isinstance(manifest.get('error', ''), str), 'invalid failure description')
    matrix, results = manifest.get('matrix', []), manifest.get('results')
    require(isinstance(matrix, list) and isinstance(results, list), 'invalid measurement collections')
    for record in [*matrix, *results]:
        require(isinstance(record, dict) and all(isinstance(record.get(name), str) and record[name]
                for name in ('case', 'implementation', 'operation')), 'invalid measurement identity')
    for result in results:
        require(isinstance(result.get('error', ''), str), 'invalid failure description')
        require(type(result.get('repetition')) is int and result['repetition'] >= 0
                and result.get('status') in ('failed', 'measured', 'passed'), 'invalid measurement state')
    require(manifest.get('observation') in ('timing', 'execution_counts'), 'invalid observation mode')
    options = manifest.get('compiler_options')
    require(isinstance(options, list) and all(isinstance(value, str) and value in (
        '--no-simplify', '--no-finite-bulk', '--release-storage',
        '--fuse-vector-reductions', '--fuse-collect-fold') for value in options),
        'invalid compiler options')
    if manifest['status'] != 'passed':
        return
    processes, plan = manifest.get('processes'), manifest.get('plan')
    require(type(processes) is int and processes > 0 and isinstance(plan, dict), 'invalid measurement plan')
    for name, minimum in (('samples', 1), ('warmups', 0), ('iterations', 1)):
        require(type(plan.get(name)) is int and plan[name] >= minimum, f'invalid plan {name}')
    matrix, results = manifest.get('matrix'), manifest.get('results')
    require(isinstance(matrix, list) and matrix and isinstance(results, list), 'missing measurement matrix')
    expected = {}
    for job in matrix:
        require(isinstance(job, dict), 'invalid matrix job')
        for name in ('case', 'implementation', 'operation', 'boundary'):
            require(isinstance(job.get(name), str) and job[name], f'invalid job {name}')
        for repetition in range(processes):
            key = (job['case'], job['implementation'], job['operation'], repetition)
            require(key not in expected, 'duplicate matrix job')
            expected[key] = job
    seen = set()
    for result in results:
        require(isinstance(result, dict) and result.get('status') == 'passed', 'unsuccessful measurement in successful run')
        key = tuple(result.get(name) for name in ('case', 'implementation', 'operation', 'repetition'))
        require(all(isinstance(value, str) for value in key[:3]) and type(key[3]) is int, 'invalid result identity')
        require(key in expected and key not in seen, 'unexpected or duplicate measurement')
        seen.add(key)
        job = expected[key]
        validate_worker(result.get('worker'), plan, job['boundary'])
        if job['boundary'] == 'admitted_entry_call':
            require(isinstance(job.get('backend'), dict), 'missing preparation request')
            validate_preparation_limits(result['worker']['lifecycle']['preparation_limits'], job['backend'])
        require(result['worker']['build'].get('execution_counts', False) is (manifest['observation'] == 'execution_counts'),
                'manifest observation capability mismatch')
    require(seen == expected.keys(), 'incomplete successful measurement matrix')


def distribution(values):
    median = statistics.median(values)
    return {'min': min(values), 'median': median, 'max': max(values),
            'mad': statistics.median(abs(v - median) for v in values)}


def summarize(manifest):
    validate_manifest(manifest)
    groups = defaultdict(list)
    for job in manifest.get('matrix', []):
        groups[job['case'], job['implementation'], job['operation']]
    for result in manifest['results']:
        groups[result['case'], result['implementation'], result['operation']].append(result)
    rows = []
    for (case, implementation, operation), results in groups.items():
        row = {'case': case, 'implementation': implementation, 'operation': operation,
               'processes': len(results), 'status': 'failed'}
        # Missing workers, later correctness failures and changed inputs invalidate timings.
        if manifest['status'] == 'passed' and len(results) == manifest['processes'] and all(
                r['status'] == 'passed' for r in results):
            row['status'] = 'passed'
            if manifest['observation'] == 'execution_counts':
                row['execution_counts'] = summarize_counts(results)
                sequences = [[(c['input_index'], c['execution_counts']) for c in r['worker']['lifecycle']['calls']] for r in results]
                row['counts_repeatable'] = all(s == sequences[0] for s in sequences[1:]) if len(sequences) > 1 else None
                rows.append(row)
                continue
            medians = [statistics.median(s['elapsed_ns']/s['iterations'] for s in r['worker']['samples']
                                        if s['phase'] == 'sample') for r in results]
            row['ns_per_call'] = distribution(medians)
            row['first_call_ns'] = distribution([r['worker']['samples'][0]['first_call_ns'] for r in results])
            row['cpu_ns_per_call'] = distribution([statistics.median(s['cpu_ns']/s['iterations'] for s in r['worker']['samples']
                                                     if s['phase'] == 'sample') for r in results])
            row['boundary'] = results[0]['worker']['boundary']
            for name in ('proof_bytes', 'admission_ns', 'process_peak_rss_bytes'):
                values = [r['worker'][name] for r in results]
                row[name] = distribution(values) if all(v is not None for v in values) else None
            row.update(summarize_lifecycle(results, manifest['plan']))
        rows.append(row)
    return rows


def summarize_lifecycle(results, plan):
    row = {}
    lifecycles = [r['worker']['lifecycle'] for r in results]
    if all(life is not None for life in lifecycles):
        row['lifecycle'] = {name: distribution([life[name] for life in lifecycles]) if all(life[name] is not None for life in lifecycles) else None
            for name in ('capture_ns', 'admit_ns', 'diagnostics_ns', 'peak_rss_before_diagnostics', 'peak_rss_after_diagnostics')}
        row['decode_ns_per_call'] = distribution([statistics.median(c['decode_ns'] for c in life['calls'][
            plan['warmups']*plan['iterations']:]) for life in lifecycles])
        if all('preparation' in life['calls'][-1] for life in lifecycles):
            row['preparation'] = {name: distribution([life['calls'][-1]['preparation'][name] for life in lifecycles])
                                  for name in ('entries', 'retained_bytes', 'hits')}
        # Distinct statements remain separately visible. Pooled schedule
        # medians above describe that declared schedule, not a batch API.
        indices = sorted({c['input_index'] for c in lifecycles[0]['calls']})
        row['inputs'] = []
        for index in indices:
            per_process, first_visits = [], []
            for result, lifecycle in zip(results, lifecycles, strict=True):
                matching = [(sample, lifecycle['calls'][i*sample['iterations']])
                            for i, sample in enumerate(result['worker']['samples'])
                            if lifecycle['calls'][i*sample['iterations']]['input_index'] == index]
                first_visits.append(matching[0][0]['first_call_ns'])
                per_process.append(statistics.median(s['elapsed_ns']/s['iterations'] for s, _ in matching if s['phase'] == 'sample'))
            row['inputs'].append({'input_index': index, 'ns_per_call': distribution(per_process),
                                  'first_visit_ns': distribution(first_visits)})
    return row


def publish(directory, manifest):
    rows = summarize(manifest)
    comparisons = paired_comparisons(manifest)
    write_json(directory / 'manifest.json', manifest)
    write_json(directory / 'summary.json', {'format': FORMAT, 'status': manifest['status'], 'rows': rows,
                                           'comparisons': comparisons})
    with (directory / 'summary.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=['case', 'implementation', 'operation', 'status',
                                                   'processes', 'boundary', 'median_ns', 'mad_ns',
                                                   'proof_bytes', 'peak_rss_bytes'])
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row[k] for k in ('case', 'implementation', 'operation', 'status', 'processes')}
                            | {'boundary': row.get('boundary'),
                               'median_ns': row.get('ns_per_call', {}).get('median'),
                               'mad_ns': row.get('ns_per_call', {}).get('mad'),
                               'proof_bytes': (row.get('proof_bytes') or {}).get('median'),
                               'peak_rss_bytes': (row.get('process_peak_rss_bytes') or {}).get('median')})
    if manifest['observation'] == 'execution_counts':
        lines = ['# Execution counts', '', f"Run status: **{manifest['status']}**.", '',
                 'Instrumented execution: timing comparisons are intentionally omitted.',
                 'See summary.json for distinct count vectors, input identities, first visits and multiplicities.',
                 'counts_repeatable compares complete ordered count sequences across processes (null with one process); false requires investigation before fitting a deterministic cost model.',
                 'Raw commands, outputs, diagnostics and incidental clock readings remain in manifest.json.', '']
        lines += failure_lines(manifest)
        (directory / 'report.md').write_text('\n'.join(lines))
        return
    lines = ['# Execution measurements', '', f"Run status: **{manifest['status']}**.", '',
             'Repeated-call times are medians of process medians; ranges span those process medians.',
             'First call is the first invocation, including the first warmup when warmups are enabled.', '',
             '| Case | Implementation | Operation | Repeated (ms) | Range (ms) | First (ms) | Proof bytes |',
             '|---|---|---|---:|---:|---:|---:|']
    successful = [row for row in rows if row['status'] == 'passed']
    for row in successful:
        value = row['ns_per_call']
        lines.append(f"| {row['case']} | {row['implementation']} | {row['operation']} | "
                     f"{value['median']/1e6:.6f} | {value['min']/1e6:.6f}–{value['max']/1e6:.6f} | "
                     f"{row['first_call_ns']['median']/1e6:.6f} | {row['proof_bytes']['median']} |")
    lines += ['', '## Timing boundaries', '']
    for case, contract in manifest['contracts'].items():
        boundaries = ', '.join(f"{name}: `{value}`" for name, value in contract.get('boundaries', {}).items())
        lines.append(f"- **{case}** — {boundaries}. {' '.join(contract.get('notes', []))}".rstrip())
    lines += ['', '## Admission, CPU time and memory', '',
              'CPU/wall is the ratio of median process CPU time to median wall time. RSS includes setup and all calls, but is sampled before final report serialization.', '',
              '| Case | Implementation | Operation | Admission (ms) | CPU/wall | Peak RSS (MiB) |',
              '|---|---|---|---:|---:|---:|']
    for row in successful:
        admission, rss = row['admission_ns'], row['process_peak_rss_bytes']
        admission = f"{admission['median']/1e6:.6f}" if admission else '—'
        rss = f"{rss['median']/2**20:.2f}" if rss else '—'
        lines.append(f"| {row['case']} | {row['implementation']} | {row['operation']} | {admission} | "
                     f"{row['cpu_ns_per_call']['median']/row['ns_per_call']['median']:.3f} | {rss} |")
    lines += ['', '## Host lifecycle', '',
              'Separate boundaries; do not add their medians to estimate end-to-end latency. Diagnostics are materialized once after the final call.', '',
              '| Case | Implementation | Operation | Capture (ms) | Admit (ms) | Decode/call (ms) | Diagnostics (ms) | RSS before/after diagnostics (MiB) |',
              '|---|---|---|---:|---:|---:|---:|---|']
    for row in successful:
        if 'lifecycle' not in row:
            continue
        life = row['lifecycle']
        times = [life['capture_ns'], life['admit_ns'], row['decode_ns_per_call'], life['diagnostics_ns']]
        rss = [life[n] for n in ('peak_rss_before_diagnostics', 'peak_rss_after_diagnostics')]
        lines.append(f"| {row['case']} | {row['implementation']} | {row['operation']} | "
                     + ' | '.join(f"{v['median']/1e6:.6f}" for v in times) + ' | '
                     + ' / '.join(f"{v['median']/2**20:.2f}" if v else '—' for v in rss) + ' |')
    prepared = [row for row in successful if 'preparation' in row]
    if prepared:
        lines += ['', '## Preparation store', '',
                  'Final per-process observations. Hits do not by themselves establish a timing benefit.', '',
                  '| Case | Implementation | Operation | Entries (median) | Retained bytes (median) | Hits (median) |',
                  '|---|---|---|---:|---:|---:|']
        for row in prepared:
            stats = row['preparation']
            lines.append(f"| {row['case']} | {row['implementation']} | {row['operation']} | "
                         + ' | '.join(str(stats[n]['median']) for n in ('entries', 'retained_bytes', 'hits')) + ' |')
    changing = [row for row in successful if len(row.get('inputs', [])) > 1]
    if changing:
        lines += ['', '## Distinct statements', '', 'One admitted Entry; round-robin calls, not batch verification.', '',
                  '| Case | Implementation | Operation | Input | First visit (ms) | Repeated (ms) |', '|---|---|---|---:|---:|---:|']
        for row in changing:
            for value in row['inputs']:
                lines.append(f"| {row['case']} | {row['implementation']} | {row['operation']} | {value['input_index']} | "
                             f"{value['first_visit_ns']['median']/1e6:.6f} | {value['ns_per_call']['median']/1e6:.6f} |")
    if manifest['status'] == 'passed':
        lines += ['', '## Preparation and CLI observations', '',
                  'External-comparison compilation includes CLI/project capture and publication. Generated-source compilation uses the compiler directly; its contract records this boundary. CLI proof calls are single exploratory observations.', '',
                  '| Family | Compilation median (ms) | Range (ms) |', '|---|---:|---:|']
        for family, records in manifest.get('compilation', {}).items():
            value = distribution([r['wall_seconds']*1000 for r in records])
            lines.append(f"| {family} | {value['median']:.3f} | {value['min']:.3f}–{value['max']:.3f} |")
        lines += ['', '| Case | CLI prove (ms) | CLI verify (ms) |', '|---|---:|---:|']
        for case, value in manifest.get('cli', {}).items():
            lines.append(f"| {case} | {value['prove_wall_seconds']*1000:.3f} | {value['verify_wall_seconds']*1000:.3f} |")
    lines += ['', '## Paired comparisons', '',
              'Ratios compare complete implementation stacks in adjacent process pairs. They are descriptive, not significance tests.', '',
              '| Case | Operation | Numerator / denominator | Median ratio | Range |', '|---|---|---|---:|---:|']
    for row in comparisons:
        value = row['ratio']
        lines.append(f"| {row['case']} | {row['operation']} | {row['numerator']} / {row['denominator']} | "
                     f"{value['median']:.3f} | {value['min']:.3f}–{value['max']:.3f} |")
    lines += failure_lines(manifest)
    lines += ['', 'See `manifest.json` for inputs, build identities, raw results and command journal paths.', '']
    (directory / 'report.md').write_text('\n'.join(lines))


def failure_lines(manifest):
    lines = []
    if manifest['status'] != 'passed':
        lines += ['', '## Incomplete or failed evidence', '',
                  'No comparison is published for this run.', '', manifest.get('error', '')]
        for result in manifest['results']:
            if result['status'] != 'passed':
                lines.append(f"- {result['case']} / {result['implementation']} / {result['operation']} / "
                             f"process {result['repetition']}: {result.get('error', result['status'])}")
    return lines


def paired_comparisons(manifest):
    validate_manifest(manifest)
    if manifest['status'] != 'passed' or manifest['observation'] == 'execution_counts': return []
    values = {(r['case'], r['implementation'], r['operation'], r['repetition']):
              statistics.median(s['elapsed_ns']/s['iterations'] for s in r['worker']['samples'] if s['phase'] == 'sample')
              for r in manifest['results'] if r['status'] == 'passed'}
    result = []
    for pair in manifest.get('comparisons', []):
        keys = [(pair['case'], impl, pair['operation'], repetition)
                for impl in (pair['numerator'], pair['denominator']) for repetition in range(manifest['processes'])]
        require(all(k in values for k in keys), 'incomplete paired comparison')
        ratios = [values[pair['case'], pair['numerator'], pair['operation'], i]
                  / values[pair['case'], pair['denominator'], pair['operation'], i]
                  for i in range(manifest['processes'])]
        result.append(pair | {'ratio': distribution(ratios),
                             'boundaries': manifest['contracts'][pair['case']]['boundaries']})
    return result


def compare(baseline, current):
    for document in (baseline, current):
        validate_manifest(document)
        require(document['observation'] == 'timing', 'timing comparison refuses instrumented execution')
        require(document.get('status') == 'passed',
                'comparison requires two successful complete runs')
    for name in ('contracts', 'plan', 'processes', 'host'):
        require(baseline[name] == current[name], f'comparison {name} differ')
    def limits(document):
        return {tuple(r[name] for name in ('case', 'implementation', 'operation', 'repetition')):
                r['worker']['lifecycle']['preparation_limits'] for r in document['results']
                if r['worker']['lifecycle'] is not None}
    require(limits(baseline) == limits(current), 'comparison preparation limits differ')
    def index(document):
        return {(r['case'], r['implementation'], r['operation']): r for r in summarize(document)}
    left, right = index(baseline), index(current)
    require(left.keys() == right.keys(), 'comparison workload matrix differs')
    ratios = []
    for key, a in left.items():
        b = right[key]
        require(a['boundary'] == b['boundary'], 'comparison timing boundaries differ')
        ratio = b['ns_per_call']['median']/a['ns_per_call']['median']
        require(math.isfinite(ratio) and ratio > 0, 'invalid ratio')
        ratios.append({'case': key[0], 'implementation': key[1], 'operation': key[2],
                       'current_over_baseline': ratio})
    return {'format': FORMAT, 'ratios': ratios,
            'compiler_options': {'baseline': baseline['compiler_options'],
                                 'current': current['compiler_options']},
            'meaning': 'ratio of medians of process medians; descriptive, no significance test'}
