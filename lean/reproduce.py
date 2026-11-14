#!/usr/bin/env python3
"""Rebuild declared source packages without prior Lean build objects.

The pinned installed Lean/Std toolchain remains trusted. Git object caches may
supply dependency sources; compiled caches never enter the reproduced package.
"""

import argparse
import hashlib
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
from support.invocation import command as lean_command
from support.compatibility import prepare
from support.packages import (PACKAGES, NAMES, DIRECTORIES, AUDITOR_OWNER, add_selection, selection,
                              selected, audited, package_directory, package_modules, module_path,
                              check_closure, test_arguments)


HERE = Path(__file__).resolve().parent
# The Clean producer's maintained output, consumed by native integration tests.
CLEAN_CONTROL = Path('../common/tests/fixtures/clean/air-control.json')


def build_inputs(root, packages=None):
    """Hash selected source scopes and the complete shared checking harness."""
    files = {root / 'reproduce.py'}
    for directory in ('checks', 'support', 'clients'):
        files.update(path for path in (root / directory).rglob('*')
                     if path.suffix in ('.py', '.lean') and
                     not any(part.startswith('.') for part in path.relative_to(root).parts))
    # A shared toolchain selector may exist for harness consumers, but no root
    # lakefile, root manifest or broad Zkc library is a maintained build input.
    if (root / 'lean-toolchain').is_file():
        files.add(root / 'lean-toolchain')
    names = selected(packages)
    for name in names:
        package = package_directory(name, root)
        files.update(package / filename for filename in
                     ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'))
        files.update(package_modules(name, root).values())
        # Test modules read their package's data fixtures while they elaborate.
        fixtures = package / 'fixtures'
        if fixtures.is_dir():
            files.update(path for path in fixtures.rglob('*') if path.is_file())
        declaration = package / 'compatibility.json'
        if declaration.is_file():
            config = json.loads(declaration.read_text())
            patch = Path(config['patch'])
            if patch.is_absolute() or '..' in patch.parts:
                raise ValueError(f'nonlocal dependency patch: {declaration}')
            files.update((declaration, package / patch))
    if 'clean' in names:
        files.add(root / CLEAN_CONTROL)
    return {str(path.relative_to(root)): support.lake.sha(path) for path in sorted(files)}


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


def prepare_dependencies(work, caches, packages=None):
    pins, sources = {}, {}
    providers = {NAMES[name]: package_directory(name, work).resolve() for name in PACKAGES}
    for name in selected(packages):
        optional = package_directory(name, work)
        check_closure(name, optional)
        manifest = json.loads((optional / 'lake-manifest.json').read_text())
        targets = optional / '.lake/packages'
        targets.mkdir(parents=True)
        for package in manifest['packages']:
            if package['type'] == 'path':
                target = (optional / package['dir']).resolve()
                if package['name'] not in providers or target != providers[package['name']]:
                    raise ValueError('unexpected maintained path dependency')
                config = tomllib.loads((target / 'lakefile.toml').read_text())
                if config['name'] != package['name']:
                    raise ValueError('maintained path provider mismatch')
                continue
            dependency = package['name'].removeprefix('«').removesuffix('»')
            pin = (package['url'].removesuffix('.git'), package['rev'])
            if package['name'] in pins:
                if pins[package['name']] != pin:
                    raise ValueError(f'incompatible shared dependency: {dependency}')
                (targets / dependency).symlink_to(sources[package['name']])
            else:
                materialize(package, targets, caches)
                pins[package['name']] = pin
                sources[package['name']] = targets / dependency
        # Retain exact-revision and per-file digest validation for declared patches.
        prepare(optional)
    return {name: {'url': url, 'revision': rev} for name, (url, rev) in pins.items()}


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


def clean_control(lake, directory, expected, log_path, env):
    """The fresh Clean producer must print exactly the maintained control."""
    with log_path.open('w') as log:
        result = subprocess.run(lean_command(directory, '-DautoImplicit=false', '-DwarningAsError=true',
                                             '--run', control_source(directory), lake=lake),
                                cwd=directory, env=env, stdout=subprocess.PIPE, stderr=log)
    produced = hashlib.sha256(result.stdout).hexdigest()
    return {'status': 'pass' if result.returncode == 0 and result.stdout == expected.read_bytes() else 'fail',
            'exit_code': result.returncode, 'sha256': produced,
            'expected': str(CLEAN_CONTROL), 'expected_sha256': support.lake.sha(expected)}


def control_source(directory):
    # Select the producer exactly; its generated audit module also ends in Control.
    source = module_path('Zkc.Tests.Clean.Control', directory.parents[1])
    if not source.is_file():
        raise ValueError(f'missing maintained Clean control producer: {source}')
    return source


def run_clients(lake, work, output, packages, env):
    options = [option for name in packages for option in ('--package', name)]
    result = subprocess.run(['python3', 'checks/check_clients.py', '--lake', lake,
                             '--output', str(output), *options], cwd=work, env=env, check=False)
    receipt = output / 'result.json'
    if result.returncode != 0 or not receipt.is_file():
        return {'status': 'fail', 'exit_code': result.returncode}
    return json.loads(receipt.read_text())


def required_markers(name):
    if not audited(name):
        # The package cannot import the auditor; its consumer audit requires these markers.
        return []
    markers = [name.upper() + '-AUDIT-PASS', 'DEPENDENCY-AUDIT-PASS']
    if name == 'arklib':
        markers.extend(['STARK-POWER-UPSTREAM-AXIOMS-PASS',
                        'STARK-EXCLUDED-COMBINATION-CONTROL-PASS', 'STARK-ARKLIB-BOUNDARY-PASS',
                        'FRI-JOHNSON-UPSTREAM-BOUNDARY-PASS'])
    if name == 'clean':
        markers.append('CLEAN-UPSTREAM-BOUNDARY-PASS')
    if name == 'verification':
        markers.append('REGISTRY-AUDIT-PASS')
    return markers


def package_tests(lake, name, directory, log_path, env):
    """Run the test driver of a package that has one."""
    arguments = test_arguments(name, directory.parents[len(Path(DIRECTORIES[name]).parts) - 1], env)
    if arguments is None:
        return {'status': 'not-applicable'}
    with log_path.open('w') as log:
        result = subprocess.run([lake, 'test', *arguments], cwd=directory, env=env,
                                stdout=log, stderr=subprocess.STDOUT)
    return {'status': 'pass' if result.returncode == 0 else 'fail', 'exit_code': result.returncode,
            'arguments': arguments, 'log_sha256': support.lake.sha(log_path)}


def consumer_audit(lake, work, output, name, env):
    """Audit a package outside Program's closure in a workspace that also requires Program."""
    result = subprocess.run(['python3', 'checks/check_consumer_audit.py', '--lake', lake,
                             '--package', name, '--output', str(output)], cwd=work, env=env,
                            stdout=subprocess.DEVNULL, check=False)
    receipt = output / 'result.json'
    if not receipt.is_file():
        return {'status': 'fail', 'exit_code': result.returncode}
    return json.loads(receipt.read_text())['packages'][name] | {'exit_code': result.returncode}


def run(args):
    names = selection(args)
    if not names:
        raise ValueError('no packages selected for reproduction')
    # A package outside Program's closure is built and tested without Program, then
    # audited in a workspace that also requires Program, whose sources and dependencies
    # are therefore prepared, though Program itself is not built.
    tools = [AUDITOR_OWNER] if AUDITOR_OWNER not in names and not all(map(audited, names)) else []
    # Source enumeration fails before output creation if migration is incomplete.
    inputs = build_inputs(HERE, names + tools)
    output = args.output.resolve()
    if output == HERE or HERE in output.parents:
        raise ValueError('the independent output must be outside the formal harness')
    output.mkdir(parents=True, exist_ok=False)
    work = output / 'lean'
    for name in inputs:
        target = work / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(HERE / name, target)
    caches = [path.resolve() for path in [args.dependency_cache, *args.integration_dependency_cache] if path]
    pins = prepare_dependencies(work, caches, names + tools)
    options = [option for name in names for option in ('--package', name)]
    env = dict(os.environ)
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME']:
        env.pop(key, None)
    lake = str(Path(support.lake.resolve(args.lake)).absolute())
    # The toolchain pin is shared: the harness selector, when present, holds it, every
    # prepared package repeats it, and Lean's version is read in the first selected package.
    selector = work / 'lean-toolchain'
    if not selector.is_file():
        selector = package_directory(names[0], work) / 'lean-toolchain'
    toolchain = selector.read_text().strip()
    for name in names + tools:
        if (package_directory(name, work) / 'lean-toolchain').read_text().strip() != toolchain:
            raise ValueError(f'{name}: toolchain differs from the shared pin')
    env['ELAN_TOOLCHAIN'] = toolchain
    version = subprocess.check_output([lake, 'env', 'lean', '--version'],
                                      cwd=package_directory(names[0], work), env=env, text=True).strip()
    expected = toolchain.split(':v')[-1]
    found = re.search(r'version (\d+\.\d+\.\d+)', version)
    if found is None or found[1] != expected:
        raise ValueError(f'wrong Lean toolchain: {version}; expected {expected}')
    for script, filename in (('check_library.py', 'boundaries.json'),
                             ('check_package_ownership.py', 'package-ownership.json')):
        with (output / filename).open('w') as stream:
            subprocess.run(['python3', 'checks/' + script, '--lake', lake, *options],
                           cwd=work, env=env, check=True, stdout=stream)
    subprocess.run(['python3', 'checks/audit_imports.py', *options], cwd=work, env=env, check=True)
    start = time.monotonic()
    runs = {}
    for name in names:
        directory = package_directory(name, work)
        runs[name] = checked_build(lake, directory, output / f'{name}-build.log', env, required_markers(name))
        if runs[name]['status'] == 'pass' and not audited(name):
            runs[name]['tests'] = package_tests(lake, name, directory, output / f'{name}-tests.log', env)
            runs[name]['consumer_audit'] = consumer_audit(lake, work, output / f'{name}-consumer-audit', name, env)
            if not all(runs[name][part]['status'] in ('pass', 'not-applicable')
                       for part in ('tests', 'consumer_audit')):
                runs[name]['status'] = 'fail'
        if runs[name]['status'] != 'pass':
            break
    control = {'status': 'not-run'}
    if runs.get('clean', {}).get('status') == 'pass':
        control = clean_control(lake, package_directory('clean', work), work / CLEAN_CONTROL,
                                output / 'clean-control.log', env)
    clients = {'status': 'not-run'}
    complete = set(runs) == set(names) and all(run['status'] == 'pass' for run in runs.values())
    with_clients = [name for name in names if audited(name)]
    if complete and with_clients:
        clients = run_clients(lake, work, output / 'clients', with_clients, env)
    elif complete:
        # Only packages that reach Program have standalone clients.
        clients = {'status': 'not-applicable'}
    changed = (build_inputs(work, names + tools) != inputs or
               build_inputs(HERE, names + tools) != inputs)
    passed = (complete and not changed and clients['status'] in ('pass', 'not-applicable')
              and ('clean' not in names or control['status'] == 'pass'))
    record = {
        'format': 'zkc.formal-reproduction.v0', 'status': 'pass' if passed else 'fail',
        'packages': names, 'audit_tools': tools, 'source_drift': changed,
        'elapsed_seconds': round(time.monotonic() - start, 2), 'lake_executable': lake,
        'toolchain': toolchain, 'lean_version': version,
        'build_inputs': inputs, 'builds': runs, 'clean_control': control, 'clients': clients,
        'external_source_pins': pins,
        'dependency_compatibility': {
            DIRECTORIES[name]: json.loads((package_directory(name, work) / 'compatibility.json').read_text())
            for name in names if (package_directory(name, work) / 'compatibility.json').is_file()},
        'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'prior_lean_build_objects': False,
        'dependency_source_transport': 'local Git objects' if caches else 'manifest URLs',
        'audit_scope': {name: list(PACKAGES[name][1]) for name in names},
        'scope': 'all stored declarations including private bodies in selected library, tools and tests; '
                 'exact pinned dependencies and installed Lean/Std toolchain; '
                 'no native correctness or protocol claim beyond the checked propositions',
    }
    (output / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k not in {'build_inputs', 'external_source_pins'}}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-cache', type=Path)
    parser.add_argument('--integration-dependency-cache', type=Path, action='append', default=[],
                        help='Git source cache of an optional package; repeat for each')
    add_selection(parser)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    existed = args.output.exists()
    try:
        run(args)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        failure = {'format': 'zkc.formal-reproduction-failure.v0', 'status': 'fail',
                   'stage': 'preparation-or-validation', 'error': str(error)}
        if not existed and args.output.is_dir():
            (args.output / 'failure.json').write_text(json.dumps(failure, indent=2) + '\n')
        print(json.dumps(failure, indent=2))
        raise SystemExit(1) from error
