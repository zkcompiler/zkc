#!/usr/bin/env python3
"""Check exact dependency closure, source ownership and architectural imports."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.lean_headers import HeaderParser
from support.packages import (LEAN, PACKAGES, NAMES, add_selection, selection,
                              selected, package_directory, package_modules,
                              library_globs, is_owned_module, check_closure)
from support.dependencies import audit_graph, permitted  # noqa: F401 -- enforcement controls


def check_owned_imports(graph):
    for owner, imports in graph.items():
        for dependency in imports:
            if is_owned_module(dependency) and dependency not in graph:
                raise ValueError(f'unselected or missing owned import: {owner} -> {dependency}')


def check(packages, lake):
    names = selected(packages)
    pins, graph, source_hashes, import_edges = {}, {}, {}, {}
    toolchain = (package_directory('program') / 'lean-toolchain').read_text()
    for name in names:
        directory, families = PACKAGES[name]
        check_closure(name, directory)
        if (directory / 'lean-toolchain').read_text() != toolchain:
            raise ValueError(f'{directory}: toolchain mismatch')
        manifest = json.loads((directory / 'lake-manifest.json').read_text())
        for dep in manifest['packages']:
            if dep['type'] == 'path':
                if not any(dep['name'] == NAMES[provider] and
                           (directory / dep['dir']).resolve() == path.resolve()
                           for provider, (path, _) in PACKAGES.items()):
                    raise ValueError(f'unexpected maintained path dependency: {directory}: {dep}')
                continue
            if dep['type'] != 'git' or not re.fullmatch('[0-9a-f]{40}', dep['rev']):
                raise ValueError(f'invalid locked pin: {dep}')
            value = (dep['url'].removesuffix('.git'), dep['rev'])
            if dep['name'] in pins and pins[dep['name']] != value:
                raise ValueError(f'conflicting pin: {dep["name"]}')
            pins[dep['name']] = value
        config = tomllib.loads((directory / 'lakefile.toml').read_text())
        targets = [entry['name'] for kind in ('lean_lib', 'lean_exe') for entry in config.get(kind, [])]
        defaults = config.get('defaultTargets', [])
        if (not targets or len(targets) != len(set(targets)) or
                len(defaults) != len(set(defaults)) or not set(defaults) <= set(targets) or
                not {entry['name'] for entry in config.get('lean_lib', [])} <= set(defaults)):
            raise ValueError(f'{directory}: default targets omit maintained libraries or contain unknown targets')
        library_globs(name, config)
        with HeaderParser(lake=lake) as headers:
            for owner, path in package_modules(name).items():
                source = path.read_text()
                import_edges[owner] = headers.details(source, path)
                graph[owner] = [entry['module'] for entry in import_edges[owner]]
                source_hashes[str(path.relative_to(LEAN))] = hashlib.sha256(path.read_bytes()).hexdigest()
                # Audits and controls deliberately use legacy imports: Lean loads
                # private bodies for them. Production modules use the module system.
                if not owner.startswith(('Zkc.Tests.', 'Zkc.Tools.')) and not headers.is_module(source, path):
                    raise ValueError(f'{path}: expected module-system source')
    check_owned_imports(graph)
    dependencies = audit_graph(graph, [root for name in names for root in PACKAGES[name][1]])
    return {'status': 'pass', 'toolchain': toolchain.strip(), 'packages': names,
            'modules': len(graph), 'dependencies': dependencies, 'pins': pins,
            'source_sha256': source_hashes, 'import_edges': import_edges}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_selection(parser)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    print(json.dumps(check(selection(args), args.lake), indent=2))


if __name__ == '__main__':
    main()
