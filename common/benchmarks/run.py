#!/usr/bin/env python3
"""Run reproducible protocol comparisons using explicit prebuilt executables."""
import argparse
import json
from pathlib import Path
import sys

from bench.io import MeasurementBusy, MeasurementError, ROOT, executable, positive_integer
from bench.results import compare, publish, validate_manifest
from bench.runner import run
from bench.suites import catalog, prepare


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
    run_parser = commands.add_parser('run', help='prepare, validate, measure and report')
    run_parser.add_argument('--source', type=Path, default=ROOT, help='project source tree (harness remains this checkout)')
    for name in ('compiler', 'runtime', 'worker'):
        run_parser.add_argument(f'--{name}', type=executable, required=True)
    run_parser.add_argument('--monero', type=executable)
    run_parser.add_argument('--monero-source', type=Path)
    run_parser.add_argument('--case', action='append', choices=[c[0] for c in catalog()])
    run_parser.add_argument('--suite', action='append', choices=sorted({c[1].name for c in catalog()}))
    run_parser.add_argument('--preset', choices=('smoke', 'stark', 'execution', 'all'), default='all')
    run_parser.add_argument('--input-count', type=positive_integer, default=1, help='distinct inputs per source proof worker; samples and warmups must cover complete cycles')
    run_parser.add_argument('--preparation-entries', type=nonnegative, help='lower the source proof store entry bound for saturation controls; byte capacity stays at its default')
    run_parser.add_argument('--preparation', choices=('enabled', 'disabled', 'both'), default='enabled', help='source proof preparation policy; external comparisons retain their standard policy')
    run_parser.add_argument('--output', type=Path, required=True)
    run_parser.add_argument('--processes', type=positive_integer, default=4)
    run_parser.add_argument('--samples', type=positive_integer, default=5)
    run_parser.add_argument('--warmups', type=nonnegative, default=2)
    run_parser.add_argument('--iterations', type=positive_integer, default=1)
    run_parser.add_argument('--threads', type=positive_integer, default=1)
    run_parser.add_argument('--seed', type=int, default=0)
    run_parser.add_argument('--cpu', type=nonnegative)
    run_parser.add_argument('--timeout', type=positive_integer, default=300)
    run_parser.add_argument('--execution-counts', action='store_true', help='require an instrumented source worker; report execution counts without timing comparisons')
    run_parser.add_argument('--compiler-option', action='append', default=[],
                            choices=['--no-simplify', '--no-finite-bulk', '--release-storage',
                                     '--fuse-vector-reductions', '--fuse-collect-fold'],
                            help='explicit compilation policy, for example --compiler-option=--fuse-collect-fold; repeat to combine')
    run_parser.add_argument('--label', default='current')
    args = parser.parse_args(argv)
    try:
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
        return run(args, prepare)
    except MeasurementBusy as error:
        print(str(error), file=sys.stderr)
        return 75
    except (MeasurementError, OSError, ValueError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
