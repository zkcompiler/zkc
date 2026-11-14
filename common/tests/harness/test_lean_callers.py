"""Package callers preserve closure order, working directories and exact pins."""

from argparse import Namespace
import json
import sys
from types import SimpleNamespace

import pytest
from harness import load


@pytest.mark.parametrize('operation', ['lean', 'fetch-lean', 'lean-fresh'])
def test_development_commands_use_inventory_selection(operation, monkeypatch, tmp_path):
    develop = load('lean_caller_develop', 'scripts/develop.py')
    args = Namespace(operation=operation, package=['ir'], core_only=False)
    calls, selections = [], []

    def selection(value):
        selections.append(value)
        return ['program', 'ir']

    inventory = SimpleNamespace(selection=selection,
                                package_directory=lambda name, root: root / name)
    monkeypatch.setattr(develop, 'lean_inventory', lambda: inventory)
    monkeypatch.setattr(develop, 'ROOT', tmp_path)
    monkeypatch.setattr(develop, 'run', lambda command, **kwargs: calls.append((command, kwargs)))
    monkeypatch.setenv('ZKC_REPORTS_DIR', str(tmp_path / 'reports'))
    if operation == "lean":
        patch = tmp_path / "lean/ir/compatibility.json"
        patch.parent.mkdir(parents=True)
        patch.write_text("{}")
    develop.execute(args)
    assert selections == [args]
    if operation == 'lean':
        assert calls == [
            (['lake', 'build'], {'cwd': tmp_path / 'lean/program'}),
            ([sys.executable, tmp_path / 'lean/support/compatibility.py', tmp_path / 'lean/ir'], {}),
            (['lake', 'build'], {'cwd': tmp_path / 'lean/ir'}),
        ]
    else:
        command, options = calls[0]
        assert len(calls) == 1 and options['cwd'] == tmp_path / 'lean'
        assert command[2:6] == ['--package', 'program', '--package', 'ir']
        assert command[6] == '--output'
        assert not {'--deps', '--with-arklib', '--with-clean'} & set(map(str, command))


def test_source_hash_refresh_reads_each_actual_package_manifest(monkeypatch, tmp_path):
    update = load('lean_caller_hashes', 'scripts/update-nix-sources.py')
    monkeypatch.syspath_prepend(str(update.NORMALIZER.parents[1] / 'lean'))
    from support import packages
    directories = {}
    originals = {}
    for index, name in enumerate(('program', 'ir', 'protocol', 'verification', 'arklib', 'clean', 'applications')):
        directory = tmp_path / 'lean' / name
        directory.mkdir(parents=True)
        manifest = directory / 'lake-manifest.json'
        pin = {'type': 'git', 'name': name, 'rev': f'{index:040x}', 'url': f'https://example.invalid/{name}'}
        manifest.write_text(json.dumps({'packages': [pin, {'type': 'path', 'name': 'zkc_program'}]}))
        originals[manifest] = manifest.read_bytes()
        directories[name] = (directory, ())
    # A package without dependencies locks nothing and contributes no source.
    core = tmp_path / 'lean/core'
    core.mkdir(parents=True)
    (core / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
    originals[core / 'lake-manifest.json'] = (core / 'lake-manifest.json').read_bytes()
    directories['core'] = (core, ())
    external = tmp_path / 'compiler/adapters/llzk/pins.json'
    external.parent.mkdir(parents=True)
    external.write_text(json.dumps({'llzk-current': {'url': 'https://example.invalid/llzk', 'revision': 'f' * 40}}))
    monkeypatch.setattr(packages, 'PACKAGES', directories)
    monkeypatch.setattr(sys, 'argv', ['update-nix-sources.py', '--root', str(tmp_path)])
    calls = []
    monkeypatch.setattr(update, 'update', lambda *args: calls.append(args))
    update.main()
    assert len(calls) == 2
    path, pins, refresh = calls[0]
    assert path == tmp_path / 'nix/lake-sources.json' and not refresh
    assert {pin['name'] for pin in pins} == set(directories) - {'core'}
    assert {pin['rev'] for pin in pins} == {f'{index:040x}' for index in range(7)}
    assert all(path.read_bytes() == original for path, original in originals.items())


def test_native_command_parsing_does_not_load_formal_inventory(monkeypatch):
    develop = load('native_without_lean_inventory', 'scripts/develop.py')
    monkeypatch.setattr(develop, 'lean_inventory', lambda: pytest.fail('native command loaded Lean inventory'))
    monkeypatch.setattr(develop, 'validate_environment', lambda: None)
    calls = []
    monkeypatch.setattr(develop, 'run', lambda args: calls.append(args))
    monkeypatch.setattr(sys, 'argv', ['develop.py', 'rust'])
    develop.main()
    assert calls == [['cargo', 'build', '--release', '--locked', '-p', 'zkc-cli', '--bin', 'zkc']]
