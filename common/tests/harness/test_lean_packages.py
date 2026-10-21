"""Manifest closure and partitioned registry controls."""
import json
import sys
from pathlib import Path

import pytest
from harness import load

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'lean'))


def test_security_manifest_closure_excludes_arklib():
    from support.packages import PACKAGES, closure
    reached = closure(PACKAGES['security'][0])
    assert {'VCVio', 'PolyFun', 'CompPoly', 'zkc'} <= reached
    assert not {'Arklib', 'zkc_arklib', 'Clean'} & reached


def test_package_selection_is_dependency_ordered():
    from support.packages import selected
    assert selected(['arklib', 'clean']) == ['main', 'security', 'arklib', 'clean']
    assert selected(['security', 'arklib']) == ['main', 'security', 'arklib']


@pytest.mark.parametrize('package,dependency', [('main', 'VCVio'), ('security', 'Arklib'),
                                              ('security', 'zkc_arklib')])
def test_package_closure_rejects_unimported_locked_dependency(tmp_path, package, dependency):
    from support.packages import check_closure
    (tmp_path / 'lakefile.toml').write_text('name = "fixture"\n')
    (tmp_path / 'lake-manifest.json').write_text(json.dumps({'packages': [
        {'type': 'git', 'name': dependency, 'rev': 'a' * 40}]}))
    with pytest.raises(ValueError, match='prohibited package closure'):
        check_closure(package, tmp_path)


def test_package_closure_rejects_transitive_path_cycle(tmp_path):
    from support.packages import closure
    for name, other in [('first', 'second'), ('second', 'first')]:
        path = tmp_path / name
        path.mkdir()
        (path / 'lakefile.toml').write_text(f'name = "{name}"\n')
        (path / 'lake-manifest.json').write_text(json.dumps({'packages': [
            {'type': 'path', 'name': other, 'dir': f'../{other}'}]}))
    with pytest.raises(ValueError, match='cyclic path dependency'):
        closure(tmp_path / 'first')


def test_manifest_provider_name_is_checked(tmp_path):
    from support.packages import closure
    provider = tmp_path / 'core'
    consumer = tmp_path / 'security'
    provider.mkdir()
    consumer.mkdir()
    (provider / 'lakefile.toml').write_text('name = "wrong"\n')
    (consumer / 'lakefile.toml').write_text('name = "security"\n[[require]]\nname = "zkc"\npath = "../core"\n')
    (consumer / 'lake-manifest.json').write_text(json.dumps({'packages': [
        {'type': 'path', 'name': 'zkc', 'dir': '../core'}]}))
    with pytest.raises(ValueError, match='provider mismatch'):
        closure(consumer)


def test_partitioned_registries_combine_and_reject_collisions():
    declarations = load('partitioned_declarations', 'lean/checks/records/declarations.py')
    entry = {'identifier': 'family.test', 'schema': 'Test.predicate'}
    records = declarations.Records(headers={
        'security': {'registry': [entry], 'endpoints': []},
        'arklib': {'registry': [entry, {'identifier': 'family.optional', 'schema': 'Optional.predicate'}]}})
    registry, endpoints = records.registry()
    assert len(registry) == 2 and endpoints == []
    records.headers['arklib']['registry'][0] = dict(entry, schema='Wrong.predicate')
    with pytest.raises(ValueError, match='conflicting registry identifier'):
        records.registry()


def test_partitioned_endpoints_reject_conflicting_theorems():
    declarations = load('partitioned_endpoints', 'lean/checks/records/declarations.py')
    endpoint = {'endpoint': 'ideal-meaning', 'property': 'soundness', 'statement': 'fixed', 'theorem': 'A'}
    records = declarations.Records(headers={
        'security': {'registry': [], 'endpoints': [endpoint]},
        'arklib': {'registry': [], 'endpoints': [dict(endpoint, theorem='B')]}})
    with pytest.raises(ValueError, match='conflicting registered endpoint'):
        records.registry()


def test_partitioned_registries_reject_schema_alias_collision():
    declarations = load('partitioned_schemas', 'lean/checks/records/declarations.py')
    records = declarations.Records(headers={
        'security': {'registry': [{'identifier': 'family.generic', 'schema': 'Shared.predicate'}]},
        'arklib': {'registry': [{'identifier': 'family.optional', 'schema': 'Shared.predicate'}]}})
    with pytest.raises(ValueError, match='conflicting registry schema'):
        records.registry()


def test_document_namespace_ownership_survives_optional_module_rename(tmp_path):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'lean/checks'))
    from records import ledger
    from records.declarations import Records
    source = tmp_path / 'lean/integrations/arklib/ZkcArkLib/Fri/Protocol.lean'
    source.parent.mkdir(parents=True)
    source.write_text('namespace ZkcSecurity.ArkLib.Fri\nend ZkcSecurity.ArkLib.Fri\n')
    document = tmp_path / 'lean/README.md'
    document.write_text('`ZkcSecurity.ArkLib.Fri.someTheorem`\n')
    subset = Records(headers={'main': {}, 'security': {}})
    assert ledger.check_documents(subset, root=tmp_path) == ([], 0, 1)
    full = Records(headers={'main': {}, 'security': {}, 'arklib': {}})
    findings, checked, skipped = ledger.check_documents(full, root=tmp_path)
    assert len(findings) == 1 and checked == 1 and skipped == 0


@pytest.mark.parametrize("returncode", [-9, -11, 0, 1])
def test_unavailable_package_requires_normal_error_exit(monkeypatch, tmp_path, returncode):
    from types import SimpleNamespace
    checker = load('package_ownership_exit_control', 'lean/checks/check_package_ownership.py')
    (tmp_path / 'lakefile.toml').write_text('name = "fixture"\n')
    monkeypatch.setattr(checker, 'PACKAGES', {'main': (tmp_path, [])})
    monkeypatch.setattr(checker, 'FORBIDDEN_DEPENDENCIES', {'main': {'Arklib'}})
    monkeypatch.setattr(checker, 'selected', lambda _: ['main'])
    monkeypatch.setattr(checker, 'check_closure', lambda *_: None)
    monkeypatch.setattr(checker.subprocess, 'run', lambda *_, **__: SimpleNamespace(
        returncode=returncode, stdout='', stderr='unknown package `Arklib`'))
    if returncode > 0:
        assert checker.check([], 'lake')['status'] == 'pass'
    else:
        with pytest.raises(ValueError, match='prohibited package available'):
            checker.check([], 'lake')
