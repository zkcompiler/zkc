#!/usr/bin/env python3
"""Run reproducible protocol comparisons using explicit prebuilt executables."""
import argparse
import copy
import json
from pathlib import Path
import sys

from bench.io import Journal, MeasurementBusy, MeasurementError, ROOT, executable, positive_integer, require
from bench.results import compare, publish, validate_manifest
from bench.runner import run
from bench.suites import catalog, prepare
from bench.configuration import flags
from bench.environment import cpu_list


def nonnegative(value):
    number = int(value)
    if number < 0: raise argparse.ArgumentTypeError('expected a nonnegative integer')
    return number


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('list', help='show maintained workloads')
    compare_parser = commands.add_parser('compare', help='compare compatible successful run manifests')
    compare_parser.add_argument('baseline', type=Path)
    compare_parser.add_argument('current', type=Path)
    report_parser = commands.add_parser('report', help='recompute summaries without remeasuring')
    report_parser.add_argument('manifest', type=Path)
    report_parser.add_argument('--output', type=Path, required=True)
    run_parser = commands.add_parser('run', help='prepare, validate, measure and report', allow_abbrev=False)
    run_parser.add_argument('--source', type=Path, default=ROOT, help='project source tree (harness remains this checkout)')
    for name in ('compiler', 'runtime', 'worker'):
        run_parser.add_argument(f'--{name}', type=executable, required=True)
    run_parser.add_argument('--monero', type=executable)
    run_parser.add_argument('--monero-source', type=Path)
    run_parser.add_argument('--c-kzg', type=executable, help='standalone pinned c-kzg benchmark client')
    run_parser.add_argument('--cargo-manifest', type=Path, action='append', default=[],
                            help='capture an offline resolved source feature graph; does not attest a prebuilt worker')
    run_parser.add_argument('--case', action='append', choices=[c[0] for c in catalog()])
    run_parser.add_argument('--suite', action='append', choices=sorted({c[1].name for c in catalog()}))
    run_parser.add_argument('--preset', choices=('smoke', 'stark', 'execution', 'all'), default='all')
    run_parser.add_argument('--ingress', choices=('json', 'wire', 'native', 'prepared'), default='json',
                            help='Host/Run input policy; reference workers keep their existing ingress')
    run_parser.add_argument('--input-count', type=positive_integer, default=1, help='distinct inputs per source proof worker; samples and warmups must cover complete cycles')
    run_parser.add_argument('--preparation-entries', type=nonnegative, help='set the source proof preparation store entry bound')
    run_parser.add_argument('--preparation-bytes', type=nonnegative, help='set the source proof preparation store byte bound')
    run_parser.add_argument('--preparation', choices=('enabled', 'disabled', 'both'), default='enabled', help='source proof preparation policy; external comparisons retain their standard policy')
    run_parser.add_argument('--output', type=Path, required=True)
    run_parser.add_argument('--processes', type=positive_integer, default=4)
    run_parser.add_argument('--samples', type=positive_integer, default=5)
    run_parser.add_argument('--warmups', type=nonnegative, default=2)
    run_parser.add_argument('--iterations', type=positive_integer, default=1)
    run_parser.add_argument('--threads', type=positive_integer, default=1)
    run_parser.add_argument('--seed', type=int, default=0)
    run_parser.add_argument('--cpus', type=cpu_list, help='CPU list/ranges, for example 2,4-7')
    run_parser.add_argument('--timeout', type=positive_integer, default=300)
    run_parser.add_argument('--execution-counts', action='store_true', help='require an instrumented source worker; report execution counts without timing comparisons')
    run_parser.add_argument('--compiler-option', action='append', default=[],
                            choices=['--no-simplify', '--no-finite-bulk', '--release-storage',
                                     '--fuse-vector-reductions', '--fuse-collect-fold', '--no-calculation-batching'],
                            help='explicit compilation policy, for example --compiler-option=--fuse-collect-fold; repeat to combine')
    run_parser.add_argument('--profile', action='append', default=[], help='compare named root build profiles; repeat for a bounded candidate panel')
    run_parser.add_argument('--profile-project', type=Path, help='manifest owning the candidate profiles')
    run_parser.add_argument('--exclusive', action='store_true',
                            help='acquire the shared measurement lock; fail with exit 75 if busy')
    run_parser.add_argument('--label', default='current')
    browser_parser = commands.add_parser('browser', help='measure prepared ordinary ProofClient cases', allow_abbrev=False)
    browser_parser.add_argument('--web', type=Path, required=True, help='client/Worker and pkg[/pkg-simd] deployment')
    browser_parser.add_argument('--cases', type=Path, required=True, help='zkc.browser-cases/0 prepared fixture document')
    browser_parser.add_argument('--node', type=executable, required=True)
    browser_parser.add_argument('--playwright', type=Path, required=True, help='explicit Playwright 1.64.1 index.mjs')
    browser_parser.add_argument('--native-example', type=executable, help='matching zkc-web memory example for bidirectional cross-verification')
    browser_parser.add_argument('--variant', action='append', choices=('portable', 'simd'))
    browser_parser.add_argument('--transport', choices=('borrowed', 'consume'), default='borrowed')
    browser_parser.add_argument('--revision', required=True, help='source revision supplied by the build owner')
    browser_parser.add_argument('--output', type=Path, required=True)
    browser_parser.add_argument('--processes', type=positive_integer, default=2)
    browser_parser.add_argument('--samples', type=positive_integer, default=5)
    browser_parser.add_argument('--warmups', type=nonnegative, default=1)
    browser_parser.add_argument('--timeout', type=positive_integer, default=300)
    browser_parser.add_argument('--exclusive', action='store_true')
    browser_parser.add_argument('--label', default='current')
    fixture_parser = commands.add_parser('browser-fixtures', help='generate captured browser source controls', allow_abbrev=False)
    fixture_parser.add_argument('--source', type=Path, default=ROOT)
    fixture_parser.add_argument('--compiler', type=executable)
    fixture_parser.add_argument('--source-only', action='store_true')
    fixture_parser.add_argument('--setup-material', type=Path, help='prepared development key material for the existing two-slot PCS fixture')
    fixture_parser.add_argument('--output', type=Path, required=True)
    fixture_parser.add_argument('--case', action='append')
    fixture_parser.add_argument('--timeout', type=positive_integer, default=300)
    args = parser.parse_args(argv)
    try:
        if args.command == 'browser-fixtures':
            require(args.source_only or args.compiler, 'browser fixture compilation requires --compiler')
            from bench.browser_fixtures import prepare as prepare_browser_fixtures
            return prepare_browser_fixtures(args)
        if args.command == 'browser':
            from bench.browser import run as run_browser
            return run_browser(args)
        if args.command == 'list':
            for name, suite, size in catalog(): print(f'{name}\t{suite.name}\t{json.dumps(size, sort_keys=True)}')
            return 0
        if args.command == 'compare':
            print(json.dumps(compare(json.loads(args.baseline.read_text()), json.loads(args.current.read_text())), indent=2))
            return 0
        if args.command == 'report':
            document = json.loads(args.manifest.read_text())
            validate_manifest(document)
            args.output.mkdir(parents=True, exist_ok=False)
            publish(args.output, document)
            return 0
        if args.profile:
            require(args.profile_project is not None and not args.compiler_option,
                    'profiles require --profile-project and cannot combine with --compiler-option')
            require(len(args.profile) <= 16 and len(set(args.profile)) == len(args.profile), 'candidate names must be distinct (at most 16)')
            require(all(name and len(name) <= 128 and all(c.isalnum() or c in '-_' for c in name) for name in args.profile), 'unsafe candidate name')
            args.output.mkdir(parents=True, exist_ok=False)
            requests = []
            candidates = []
            for name in args.profile:
                directory = args.output/'requests'/name
                journal = Journal(directory, args.timeout)
                report, _ = journal.report([args.runtime, '--json', 'inspect', '--view=project',
                    f'--project={args.profile_project.resolve()}', f'--compiler={args.compiler}', f'--profile={name}'],
                    cwd=args.source.resolve(), status='inspected')
                candidate = copy.copy(args)
                candidate.output = args.output/'candidates'/name
                candidate.label = name
                candidate.configuration = report['settings']
                candidate.compiler_option = flags(report['settings']['values'])
                requests.append({'profile':name,'settings':report['settings'],
                    'request_report':str(directory),'result':str(candidate.output/'manifest.json')})
                candidates.append(candidate)
            # Resolve the entire bounded panel before launching measurements.
            # Request journals and candidate outputs have disjoint namespaces.
            (args.output/'candidates.json').write_text(json.dumps({'format':'zkc.benchmark-candidates/0',
                'candidates':requests}, indent=2)+'\n')
            for candidate in candidates:
                status = run(candidate, prepare)
                if status: return status
            return 0
        require(args.profile_project is None, '--profile-project requires --profile')
        return run(args, prepare)
    except MeasurementBusy as error:
        print(str(error), file=sys.stderr)
        return 75
    except (MeasurementError, OSError, ValueError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
