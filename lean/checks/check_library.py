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

ROOT = Path(__file__).resolve().parents[1]
INTEGRATIONS = {'arklib': ('ZkcSecurity', 'TestsSecurity'), 'clean': ('ZkcClean', 'TestsClean')}


def below(name, root):
    return name == root or name.startswith(root + '.')


def permitted(owner, dependency):
    if below(owner, 'Zkc'):
        if any(below(dependency, root) for root in (
                'Tests', 'TestsSecurity', 'TestsClean', 'ZkcExamples', 'ZkcTools',
                'ZkcSecurity', 'ZkcClean', 'ArkLib', 'VCVio', 'Clean', 'PolyFun', 'CompPoly')):
            return False
        if not below(owner, 'Zkc.Protocols') and below(dependency, 'Zkc.Protocols'):
            return False
    if below(owner, 'ZkcSecurity') and not below(owner, 'ZkcSecurity.Examples'):
        if any(below(dependency, root) for root in ('ZkcExamples', 'Tests', 'TestsSecurity',
                'TestsClean', 'ZkcTools', 'ZkcClean', 'Clean')):
            return False
    if below(owner, 'ZkcClean'):
        if any(below(dependency, root) for root in ('Tests', 'TestsSecurity', 'TestsClean',
                'ZkcTools', 'ZkcExamples', 'ZkcSecurity', 'ArkLib', 'VCVio', 'PolyFun')):
            return False
    return True


def check(selected, lake):
    packages = [(ROOT, ('Zkc', 'ZkcExamples', 'ZkcTools', 'Tests'))]
    packages.extend((ROOT / 'integrations' / name, INTEGRATIONS[name]) for name in selected)
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
                assert directory != ROOT and dep['name'] == 'zkc' and (directory / dep['dir']).resolve() == ROOT
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
                if owner.startswith(('Zkc.', 'ZkcExamples.', 'ZkcSecurity.')):
                    assert source.startswith('module\n'), f'{path}: expected module-system source'
    for owner, dependencies in graph.items():
        pending, seen = list(dependencies), set()
        while pending:
            dependency = pending.pop()
            if dependency in seen:
                continue
            seen.add(dependency)
            assert permitted(owner, dependency), f'forbidden dependency: {owner} reaches {dependency}'
            pending.extend(graph.get(dependency, []))
    return {'status': 'pass', 'toolchain': toolchain.strip(), 'packages': len(packages),
            'modules': len(graph), 'pins': pins, 'source_sha256': source_hashes}


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
