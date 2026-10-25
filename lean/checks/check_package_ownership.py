#!/usr/bin/env python3
"""Check package providers with Lake's resolver, including absent module names.

The source inventory alone cannot detect broad overlapping roots. Query each
library glob in each consumer workspace, qualified by every local provider.
An absent sentinel must be recognized only by its intended package; Lake must
reject it as an unknown module in every other provider. The `lean` input facet
does not compile or write library output files.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.packages import PACKAGES, NAMES, FORBIDDEN_DEPENDENCIES, selected, check_closure


def check(integrations, lake):
    rows = []
    absent_packages = []
    for consumer in selected(integrations):
        directory = PACKAGES[consumer][0]
        check_closure(consumer, directory)
        for dependency in sorted(FORBIDDEN_DEPENDENCIES[consumer]):
            result = subprocess.run([lake, 'query', f'@{dependency}/+PackageBoundarySentinel:lean'],
                                    cwd=directory, capture_output=True, text=True, timeout=30)
            diagnostic = result.stdout + result.stderr
            if result.returncode <= 0 or f'unknown package `{dependency}`' not in diagnostic:
                raise ValueError(f'{consumer}: prohibited package available to Lake: {dependency}: {diagnostic}')
            absent_packages.append({'workspace': consumer, 'unavailable_package': dependency})
        providers = selected([] if consumer == 'main' else [consumer])
        for owner in providers:
            provider = PACKAGES[owner][0]
            config = tomllib.loads((provider / 'lakefile.toml').read_text())
            globs = {glob for library in config.get('lean_lib', [])
                     for glob in library.get('globs', library.get('roots', [library['name']]))}
            for glob in sorted(globs):
                broad = glob.endswith(('.+', '.*'))
                module = glob[:-2] + '.PackageBoundarySentinel' if broad else glob
                source = provider.joinpath(*module.split('.')).with_suffix('.lean')
                if broad and source.exists():
                    raise ValueError(f'sentinel unexpectedly exists: {source}')
                for candidate in providers:
                    target = f'@{NAMES[candidate]}/+{module}:lean'
                    result = subprocess.run([lake, 'query', target], cwd=directory,
                                            capture_output=True, text=True, timeout=30)
                    diagnostic = result.stdout + result.stderr
                    if candidate != owner:
                        valid = result.returncode > 0 and f'unknown module `{module}`' in diagnostic
                    elif source.exists():
                        valid = result.returncode == 0 and str(source) in diagnostic
                    else:
                        valid = result.returncode > 0 and 'no such file or directory' in diagnostic and str(source) in diagnostic
                    if not valid:
                        raise ValueError(f'{consumer}: incorrect provider {candidate} for {module}: {diagnostic}')
                rows.append({'workspace': consumer, 'module': module, 'provider': owner,
                             'source_exists': source.exists()})
    return {'status': 'pass', 'checks': rows, 'absent_packages': absent_packages}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument('--main-only', action='store_true')
    selection.add_argument('--integration', action='append', choices=('security', 'arklib', 'clean'))
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    integrations = [] if args.main_only else args.integration or ['arklib', 'clean']
    print(json.dumps(check(integrations, args.lake), indent=2))


if __name__ == '__main__':
    main()
