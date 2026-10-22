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


def check(selected, lake):
    packages = [PACKAGES[name] for name in select_packages(selected)]
    for name in select_packages(selected):
        check_closure(name, PACKAGES[name][0])
    pins, graph, source_hashes = {}, {}, {}
    import hashlib
    toolchain = (ROOT / 'lean-toolchain').read_text()
    for directory, families in packages:
        assert (directory / 'lean-toolchain').read_text() == toolchain, f'{directory}: toolchain mismatch'
        manifest = json.loads((directory / 'lake-manifest.json').read_text())
        names = set()
        for dep in manifest['packages']:
            assert dep['name'] not in names, f'duplicate dependency: {dep["name"]}'
            names.add(dep['name'])
            if dep['type'] == 'path':
                assert any(dep['name'] == package_name and (directory / dep['dir']).resolve() == provider for package_name, provider in [('zkc', ROOT), ('zkc_security', ROOT / 'security')])
                continue
            assert dep['type'] == 'git' and re.fullmatch('[0-9a-f]{40}', dep['rev']), dep
            value = (dep['url'].removesuffix('.git'), dep['rev'])
            assert dep['name'] not in pins or pins[dep['name']] == value, f'conflicting pin: {dep["name"]}'
            pins[dep['name']] = value
        if directory == ROOT:
            assert not names.intersection({'Arklib', 'VCVio', 'Clean', 'PolyFun', 'CompPoly'})
        config = tomllib.loads((directory / 'lakefile.toml').read_text())
        targets = {entry['name'] for kind in ('lean_lib', 'lean_exe') for entry in config.get(kind, [])}
        assert set(config['defaultTargets']) == targets, f'{directory}: default targets omit maintained code'
        files = [p for family in families for p in (directory / family).rglob('*.lean')]
        files += [directory / (family + '.lean') for family in families if (directory / (family + '.lean')).is_file()]
        with HeaderParser(root=directory, lake=lake) as headers:
            for path in sorted(files):
                source = path.read_text()
                owner = '.'.join(path.relative_to(directory).with_suffix('').parts)
                graph[owner] = headers.imports(source, path)
                source_hashes[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
                if owner.startswith(('Zkc.', 'ZkcExamples.', 'ZkcSecurity.', 'ZkcArkLib.')):
                    assert source.startswith('module\n'), f'{path}: expected module-system source'
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
            assert not overlap, f'overlapping Lake ownership: {owner}:{prefix} and {other}:{target}'
    for owner, imports in graph.items():
        for dep in imports:
            if dep.startswith(('ZkcSecurity.', 'ZkcArkLib.')):
                assert dep in graph, f'unselected or missing owned import: {owner} -> {dep}'
    dependencies = audit_graph(graph, [family for _, families in packages for family in families])
    return {'status': 'pass', 'toolchain': toolchain.strip(), 'packages': len(packages),
            'modules': len(graph), 'dependencies': dependencies, 'pins': pins, 'source_sha256': source_hashes}


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
