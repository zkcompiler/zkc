#!/usr/bin/env python3
"""Rebuild declared source packages without prior Lean build objects.

The pinned installed Lean/Std toolchain remains trusted. Git object caches may
supply dependency sources; compiled caches never enter the reproduced package.
"""

import argparse
import json
import os
import sys
from pathlib import Path

# Two consumer checks load this module by path rather than importing it, so
# the package directory is not on the path the way it is when this file is
# run. It puts itself there rather than requiring every loader to.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import support.lake  # noqa: E402
import re
import shutil
import subprocess
import time
import tomllib


HERE = Path(__file__).resolve().parent
INTEGRATION = Path('integrations/arklib')




def build_inputs(root, with_arklib=False):
    files = [root / name for name in (
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
        'reproduce.py', 'Zkc.lean')]
    # The checks and what they share, by looking rather than by a list: these
    # named five of them and went stale the moment the checks moved together.
    files.extend((root / 'checks').glob('*.py'))
    files.extend((root / 'support').glob('*.py'))
    for directory in ('Zkc', 'Tests', 'Examples', 'Tools'):
        files.extend((root / directory).rglob('*.lean'))
    files.append(root / 'clients/Main.lean')
    # Tests.Variant includes this shared file at compile time. Copy and hash it
    # with the package so an isolated rebuild has the same declared inputs.
    files.append(root / '../tests/fixtures/variants/history-contracts.txt')
    if with_arklib:
        files.append(root / 'clients/ArkLib.lean')
        optional = root / INTEGRATION
        files.extend(optional / name for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'))
        for directory in ('ZkcArkLib', 'TestsArkLib'):
            files.extend((optional / directory).rglob('*.lean'))
    return {str(p.relative_to(root)): support.lake.sha(p) for p in sorted(files)}


def materialize(package, packages, caches):
    name = package['name'].removeprefix('«').removesuffix('»')
    dest = packages / name
    if caches:
        origin = next((root / name for root in caches if (root / name).is_dir()), None)
        if origin is None:
            raise ValueError(f'missing declared dependency source cache: {name}')
        command = ['git', 'clone', '--quiet', '--shared', '--no-checkout', str(origin), str(dest)]
    else:
        command = ['git', 'clone', '--quiet', '--no-checkout', package['url'], str(dest)]
    subprocess.run(command, check=True)
    subprocess.run(['git', '-C', str(dest), 'checkout', '--quiet', '--detach', package['rev']], check=True)
    subprocess.run(['git', '-C', str(dest), 'remote', 'set-url', 'origin', package['url']], check=True)
    actual = subprocess.check_output(['git', '-C', str(dest), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev'] or (dest / '.lake/build').exists():
        raise ValueError(f'source/build precondition failed: {name}')


def prepare_dependencies(work, caches, with_arklib):
    manifest = json.loads((work / 'lake-manifest.json').read_text())
    packages = work / '.lake/packages'
    packages.mkdir(parents=True)
    pins = {}
    for package in manifest['packages']:
        if package['type'] != 'git':
            raise ValueError('main package dependency must be an exact Git source')
        materialize(package, packages, caches)
        pins[package['name']] = package['rev']
    if with_arklib:
        optional = work / INTEGRATION
        other = json.loads((optional / 'lake-manifest.json').read_text())
        targets = optional / '.lake/packages'
        targets.mkdir(parents=True)
        for package in other['packages']:
            if package['type'] == 'path':
                if package['name'] != 'zkc' or (optional / package['dir']).resolve() != work.resolve():
                    raise ValueError('unexpected integration path dependency')
                continue
            name = package['name'].removeprefix('«').removesuffix('»')
            if package['name'] in pins:
                if pins[package['name']] != package['rev']:
                    raise ValueError(f'incompatible shared dependency: {name}')
                (targets / name).symlink_to(packages / name)
            else:
                materialize(package, targets, caches)
                pins[package['name']] = package['rev']
    return pins


def checked_build(lake, directory, log_path, env, required):
    config = tomllib.loads((directory / 'lakefile.toml').read_text())
    targets = [entry['name'] for kind in ('lean_lib', 'lean_exe')
               for entry in config.get(kind, [])]
    if not targets:
        raise ValueError(f'no declared targets in {directory}')
    with log_path.open('w') as log:
        result = subprocess.run([lake, '--no-cache', 'build', *targets], cwd=directory, env=env,
                                stdout=log, stderr=subprocess.STDOUT)
    text = log_path.read_text()
    # Each audit reports under its own marker, so the receipt says which scope
    # each count came from; they all used to say AUDIT-PASS and be a list of
    # numbers with nothing to attach them to.
    audits = {name: {'declarations': int(declarations), 'theorems': int(theorems)}
              for name, declarations, theorems in
              re.findall(r'([A-Z][A-Z-]*AUDIT-PASS) declarations=(\d+) theorems=(\d+)', text)}
    jobs = re.search(r'Build completed successfully \((\d+) jobs\)', text)
    markers = {marker: marker in text for marker in required}
    executables = {entry['name']: directory / '.lake/build/bin' / entry['name']
                   for entry in config.get('lean_exe', [])}
    linked = all(path.is_file() and os.access(path, os.X_OK) for path in executables.values())
    return {
        'exit_code': result.returncode,
        'status': 'pass' if result.returncode == 0 and jobs and all(markers.values()) and linked else 'fail',
        'targets': targets,
        'executables': {name: support.lake.sha(path) if path.is_file() else None
                        for name, path in executables.items()},
        'lake_jobs': int(jobs[1]) if jobs else None,
        'required_markers': markers,
        'axiom_audits': audits,
        'log_sha256': support.lake.sha(log_path),
    }


def run_clients(lake, work, output, with_arklib, env):
    subprocess.run(['python3', 'checks/check_clients.py', '--lake', lake, '--output', str(output),
                    *(['--with-arklib'] if with_arklib else [])], cwd=work, env=env, check=False)
    receipt = output / 'result.json'
    return json.loads(receipt.read_text()) if receipt.is_file() else {'status': 'not-run'}


def run(args):
    output = args.output.resolve()
    if output == HERE or HERE in output.parents:
        raise ValueError('the independent output must be outside the formal package')
    output.mkdir(parents=True, exist_ok=False)
    work = output / 'formal'
    inputs = build_inputs(HERE, args.with_arklib)
    for name in inputs:
        target = work / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(HERE / name, target)
    caches = [path.resolve() for path in [args.dependency_cache, args.integration_dependency_cache] if path]
    pins = prepare_dependencies(work, caches, args.with_arklib)
    options = [] if args.with_arklib else ['--main-only']
    env = dict(os.environ)
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME']:
        env.pop(key, None)
    lake = support.lake.resolve(args.lake)
    lake = str(Path(lake).absolute())
    version = subprocess.check_output([lake, 'env', 'lean', '--version'], cwd=work, env=env, text=True).strip()
    expected = (work / 'lean-toolchain').read_text().strip().split(':v')[-1]
    found = re.search(r'version (\d+\.\d+\.\d+)', version)
    if found is None or found[1] != expected:
        raise ValueError(f'wrong Lean toolchain: {version}; expected {expected}')
    with (output / 'boundaries.json').open('w') as stream:
        subprocess.run(['python3', 'checks/check_library.py', '--lake', lake, *options], cwd=work, env=env, check=True, stdout=stream)
    subprocess.run(['python3', 'checks/audit_imports.py', *options], cwd=work, env=env, check=True)
    start = time.monotonic()
    runs = {'main': checked_build(lake, work, output / 'main-build.log', env,
            ['DEPENDENCY-AUDIT-PASS', 'FOUNDATION-AUDIT-PASS', 'SOURCE-PLAN-AUDIT-PASS'])}
    if args.with_arklib and runs['main']['status'] == 'pass':
        runs['arklib'] = checked_build(lake, work / INTEGRATION, output / 'arklib-build.log', env,
            ['DEPENDENCY-AUDIT-PASS', 'UPSTREAM-STATUS FiatShamir.euf_cma_bound:',
             'UPSTREAM-STATUS fiatShamir_completeness:'])
    clients = {'status': 'not-run'}
    if all(run['status'] == 'pass' for run in runs.values()):
        clients = run_clients(lake, work, output / 'clients', args.with_arklib, env)
    changed = build_inputs(work, args.with_arklib) != inputs or build_inputs(HERE, args.with_arklib) != inputs
    passed = (all(run['status'] == 'pass' for run in runs.values()) and not changed
              and (not args.with_arklib or 'arklib' in runs) and clients['status'] == 'pass')
    record = {
        'format': 'zkc.formal-reproduction.v3', 'status': 'pass' if passed else 'fail',
        'with_arklib': args.with_arklib, 'source_drift': changed,
        'elapsed_seconds': round(time.monotonic() - start, 2),
        'lake_executable': lake,
        'toolchain': (work / 'lean-toolchain').read_text().strip(), 'lean_version': version,
        'build_inputs': inputs, 'builds': runs, 'clients': clients, 'external_source_pins': pins,
        'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'prior_lean_build_objects': False,
        'dependency_source_transport': 'local Git objects' if caches else 'manifest URLs',
        'audit_scope': 'all stored declarations in library, tests and examples; '
                       'tool wrappers are compiled and linked, not included in the axiom inventory',
        'scope': 'declared owned source packages and pinned dependencies; installed Lean/Std toolchain; '
                 'no native correctness or protocol claim beyond the checked propositions',
    }
    (output / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k not in {'build_inputs', 'external_source_pins'}}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-cache', type=Path)
    parser.add_argument('--integration-dependency-cache', type=Path)
    parser.add_argument('--with-arklib', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    existed = args.output.exists()
    try:
        run(args)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        failure = {'format': 'zkc.formal-reproduction-failure.v2', 'status': 'fail',
                   'stage': 'preparation-or-validation', 'error': str(error)}
        if not existed and args.output.is_dir():
            (args.output / 'failure.json').write_text(json.dumps(failure, indent=2) + '\n')
        print(json.dumps(failure, indent=2))
        raise SystemExit(1) from error
