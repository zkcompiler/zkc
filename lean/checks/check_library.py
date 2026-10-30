#!/usr/bin/env python3
"""Check exact dependency closure, source ownership and architectural imports.

The separate Lean declaration audit checks proof bodies and transitive axioms.
"""
import argparse
import json
from pathlib import Path
import re
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.lean_headers import HeaderParser
from support.packages import PACKAGES, selected as select_packages, check_closure
from support.dependencies import audit_graph, permitted  # noqa: F401 -- enforcement controls

ROOT = Path(__file__).resolve().parents[1]
INTEGRATIONS = {name: roots for name, (_, roots) in PACKAGES.items() if name != 'main'}


def check_owned_imports(graph):
    """Reject retired or unselected owned modules before an expensive build."""
    owned = [root for _, roots in PACKAGES.values() for root in roots]
    for owner, imports in graph.items():
        for dependency in imports:
            if any(dependency == root or dependency.startswith(root + ".") for root in owned):
                if dependency not in graph:
                    raise AssertionError(f"unselected or missing owned import: {owner} -> {dependency}")


def check(selected, lake):
    packages = [PACKAGES[name] for name in select_packages(selected)]
    for name in select_packages(selected):
        check_closure(name, PACKAGES[name][0])
    pins, graph, source_hashes, import_edges = {}, {}, {}, {}
    import hashlib
    toolchain = (ROOT / 'lean-toolchain').read_text()
    for directory, families in packages:
        if not ((directory / 'lean-toolchain').read_text() == toolchain):
            raise AssertionError(f'{directory}: toolchain mismatch')
        manifest = json.loads((directory / 'lake-manifest.json').read_text())
        names = set()
        for dep in manifest['packages']:
            if not (dep['name'] not in names):
                raise AssertionError(f'duplicate dependency: {dep["name"]}')
            names.add(dep['name'])
            if dep['type'] == 'path':
                if not (any(dep['name'] == package_name and (directory / dep['dir']).resolve() == provider for package_name, provider in [('zkc', ROOT), ('zkc_security', ROOT / 'security')])):
                    raise AssertionError("checks/check_library.py:37: any(dep['name'] == package_name and (directory / dep['dir']).resolve() == provider for package_name, provider in [('zkc', ROOT), ('zkc_security', ROOT / 'security')])")
                continue
            if not (dep['type'] == 'git' and re.fullmatch('[0-9a-f]{40}', dep['rev'])):
                raise AssertionError(dep)
            value = (dep['url'].removesuffix('.git'), dep['rev'])
            if not (dep['name'] not in pins or pins[dep['name']] == value):
                raise AssertionError(f'conflicting pin: {dep["name"]}')
            pins[dep['name']] = value
        if directory == ROOT:
            if not (not names.intersection({'Arklib', 'VCVio', 'Clean', 'PolyFun', 'CompPoly'})):
                raise AssertionError("checks/check_library.py:44: not names.intersection({'Arklib', 'VCVio', 'Clean', 'PolyFun', 'CompPoly'})")
        config = tomllib.loads((directory / 'lakefile.toml').read_text())
        targets = {entry['name'] for kind in ('lean_lib', 'lean_exe') for entry in config.get(kind, [])}
        if not (set(config['defaultTargets']) == targets):
            raise AssertionError(f'{directory}: default targets omit maintained code')
        files = [p for family in families for p in (directory / family).rglob('*.lean')]
        files += [directory / (family + '.lean') for family in families if (directory / (family + '.lean')).is_file()]
        with HeaderParser(root=directory, lake=lake) as headers:
            for path in sorted(files):
                source = path.read_text()
                owner = '.'.join(path.relative_to(directory).with_suffix('').parts)
                import_edges[owner] = headers.details(source, path)
                graph[owner] = [entry['module'] for entry in import_edges[owner]]
                source_hashes[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
                if owner.startswith(('Zkc.', 'ZkcExamples.', 'ZkcSecurity.', 'ZkcSecurityTools.', 'ZkcSecurityExamples.', 'ZkcArkLib.', 'ZkcArkLibExamples.')):
                    if not (source.startswith('module\n')):
                        raise AssertionError(f'{path}: expected module-system source')
    ownership = []
    for directory, families in packages:
        config = tomllib.loads((directory / 'lakefile.toml').read_text())
        for library in config.get('lean_lib', []):
            roots = library.get('roots', [library['name']])
            globs = library.get('globs', roots)
            ownership += [(directory, glob.removesuffix('.+').removesuffix('.*'), glob.endswith(('.+', '.*')))
                          for glob in globs]
    for i, (owner, prefix, broad) in enumerate(ownership):
        for other, target, other_broad in ownership[:i]:
            if owner == other:
                continue
            overlap = prefix == target or broad and target.startswith(prefix + '.') or other_broad and prefix.startswith(target + '.')
            if not (not overlap):
                raise AssertionError(f'overlapping Lake ownership: {owner}:{prefix} and {other}:{target}')
    check_owned_imports(graph)
    dependencies = audit_graph(graph, [family for _, families in packages for family in families])
    return {'status': 'pass', 'toolchain': toolchain.strip(), 'packages': len(packages),
            'modules': len(graph), 'dependencies': dependencies, 'pins': pins,
            'source_sha256': source_hashes, 'import_edges': import_edges}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument('--main-only', action='store_true')
    selection.add_argument('--integration', action='append', choices=sorted(INTEGRATIONS))
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    selected = [] if args.main_only else args.integration or sorted(INTEGRATIONS)
    print(json.dumps(check(selected, args.lake), indent=2))


if __name__ == '__main__':
    main()
