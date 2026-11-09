"""Manifest closure and partitioned registry controls."""
import json
from contextlib import nullcontext
from pathlib import Path

import pytest
from harness import lean_imports, load


@pytest.fixture(autouse=True)
def isolated_lean_workspace():
    with lean_imports():
        yield


def test_verification_manifest_closure_excludes_arklib():
    from support.packages import PACKAGES, closure
    reached = closure(PACKAGES['verification'][0])
    assert {'VCVio', 'PolyFun', 'CompPoly', 'zkc_ir', 'zkc_protocol', 'zkc_program'} <= reached
    assert not {'Arklib', 'zkc_arklib', 'Clean'} & reached


def test_package_selection_is_dependency_ordered():
    from support.packages import selected
    assert selected(['arklib', 'clean']) == ['program', 'ir', 'protocol', 'arklib', 'clean']
    assert selected(['verification', 'arklib']) == ['program', 'ir', 'protocol', 'verification', 'arklib']


def test_companion_modules_are_declaration_record_inputs():
    declarations = load('companion_record_inputs', 'lean/checks/records/declarations.py')
    from support.packages import package_modules
    root, _ = declarations.PACKAGES['program']
    selected = set(package_modules('program').values())
    companions = set((root / 'Zkc/Tools/Program/Companions').rglob('*.lean'))
    assert companions
    assert companions <= selected


@pytest.mark.parametrize('package,dependency', [('ir', 'VCVio'), ('verification', 'Arklib'),
                                              ('verification', 'zkc_arklib')])
def test_package_closure_rejects_unimported_locked_dependency(tmp_path, monkeypatch, package, dependency):
    from support import packages as inventory
    from support.packages import check_closure
    (tmp_path / 'lakefile.toml').write_text(f'name = "{inventory.NAMES[package]}"\n' + ''.join(
        f'[[require]]\nname = "{inventory.NAMES[name]}"\npath = "../{name}"\n'
        for name in inventory.DEPENDENCIES[package]))
    monkeypatch.setattr(inventory, 'closure', lambda _: inventory.allowed_dependencies(package) | {dependency})
    with pytest.raises(ValueError, match='prohibited package closure'):
        check_closure(package, tmp_path)


def test_package_closure_rejects_transitive_path_cycle(tmp_path):
    from support.packages import closure
    for name, other in [('first', 'second'), ('second', 'first')]:
        path = tmp_path / name
        path.mkdir()
        (path / 'lakefile.toml').write_text(f'name = "{name}"\n')
        (path / 'lake-manifest.json').write_text(json.dumps({'name': name, 'packages': [
            {'type': 'path', 'name': other, 'dir': f'../{other}'}]}))
    with pytest.raises(ValueError, match='cyclic path dependency'):
        closure(tmp_path / 'first')


def test_manifest_provider_name_is_checked(tmp_path):
    from support.packages import closure
    provider = tmp_path / 'core'
    consumer = tmp_path / 'verification'
    provider.mkdir()
    consumer.mkdir()
    (provider / 'lakefile.toml').write_text('name = "wrong"\n')
    (consumer / 'lakefile.toml').write_text('name = "verification"\n[[require]]\nname = "zkc_ir"\npath = "../core"\n')
    (consumer / 'lake-manifest.json').write_text(json.dumps({'name': 'verification', 'packages': [
        {'type': 'path', 'name': 'zkc_ir', 'dir': '../core'}]}))
    with pytest.raises(ValueError, match='provider mismatch'):
        closure(consumer)


def test_partitioned_registries_combine_and_reject_collisions():
    declarations = load('partitioned_declarations', 'lean/checks/records/declarations.py')
    entry = {'identifier': 'family.test', 'schema': 'Test.predicate'}
    records = declarations.Records(headers={
        'verification': {'registry': [entry], 'endpoints': []},
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
        'verification': {'registry': [], 'endpoints': [endpoint]},
        'arklib': {'registry': [], 'endpoints': [dict(endpoint, theorem='B')]}})
    with pytest.raises(ValueError, match='conflicting registered endpoint'):
        records.registry()


def test_partitioned_registries_reject_schema_alias_collision():
    declarations = load('partitioned_schemas', 'lean/checks/records/declarations.py')
    records = declarations.Records(headers={
        'verification': {'registry': [{'identifier': 'family.generic', 'schema': 'Shared.predicate'}]},
        'arklib': {'registry': [{'identifier': 'family.optional', 'schema': 'Shared.predicate'}]}})
    with pytest.raises(ValueError, match='conflicting registry schema'):
        records.registry()


def test_document_namespace_ownership_survives_optional_module_rename(tmp_path):
    from records import ledger
    from records.declarations import Records
    from support.packages import PACKAGES, module_path
    # The ledger checks a complete migrated source inventory, even when only a
    # subset of its declaration records was selected.
    for _, roots in PACKAGES.values():
        for prefix in roots:
            placeholder = module_path(prefix + '.Inventory', tmp_path / 'lean')
            placeholder.parent.mkdir(parents=True, exist_ok=True)
            placeholder.write_text('module\n')
    source = tmp_path / 'lean/adapters/arklib/Zkc/Adapters/ArkLib/Fri/Protocol.lean'
    source.parent.mkdir(parents=True)
    source.write_text('namespace ZkcSecurity.ArkLib.Fri\nend ZkcSecurity.ArkLib.Fri\n')
    document = tmp_path / 'lean/README.md'
    document.write_text('`ZkcSecurity.ArkLib.Fri.someTheorem`\n')
    subset = Records(headers={'program': {}, 'ir': {}, 'protocol': {}, 'verification': {}})
    assert ledger.check_documents(subset, root=tmp_path) == ([], 0, 1)
    full = Records(headers={'program': {}, 'ir': {}, 'protocol': {}, 'verification': {}, 'arklib': {}})
    findings, checked, skipped = ledger.check_documents(full, root=tmp_path)
    assert len(findings) == 1 and checked == 1 and skipped == 0


@pytest.mark.parametrize("returncode", [-9, -11, 0, 1])
def test_unavailable_package_requires_normal_error_exit(monkeypatch, tmp_path, returncode):
    from types import SimpleNamespace
    checker = load('package_ownership_exit_control', 'lean/checks/check_package_ownership.py')
    (tmp_path / 'lakefile.toml').write_text('name = "fixture"\n')
    monkeypatch.setattr(checker, 'PACKAGES', {'ir': (tmp_path, [])})
    monkeypatch.setattr(checker, 'FORBIDDEN_DEPENDENCIES', {'ir': {'Arklib'}})
    monkeypatch.setattr(checker, 'selected', lambda _: ['ir'])
    monkeypatch.setattr(checker, 'check_closure', lambda *_: set())
    monkeypatch.setattr(checker.subprocess, 'run', lambda *_, **__: SimpleNamespace(
        returncode=returncode, stdout='', stderr='unknown package `Arklib`'))
    if returncode > 0:
        monkeypatch.setattr(checker, 'library_globs', lambda *_: [])
        assert checker.check([], 'lake')['status'] == 'pass'
    else:
        with pytest.raises(ValueError, match='prohibited package available'):
            checker.check([], 'lake')


@pytest.mark.parametrize('package,prefix', [
    ('program', 'Zkc.Program'), ('ir', 'Zkc.IR'), ('protocol', 'Zkc.Protocol'),
    ('verification', 'Zkc.Verification'), ('arklib', 'Zkc.Adapters.ArkLib'),
    ('clean', 'Zkc.Adapters.Clean'), ('applications', 'Zkc.Applications'),
])
def test_full_module_prefix_has_one_exclusive_owner(package, prefix):
    from support.packages import PACKAGES, module_owner, is_owned_module
    for root in PACKAGES[package][1]:
        assert module_owner(root) == module_owner(root + '.MissingSentinel') == package
        assert is_owned_module(root)
        assert not is_owned_module(root + 'Extra')
        with pytest.raises(ValueError, match='no maintained package'):
            module_owner(root + 'Extra')
    assert prefix in PACKAGES[package][1]


@pytest.mark.parametrize('module', ['Zkc', 'Zkc.Tools', 'Zkc.Tests', 'Zkc.Adapters',
                                    'ZkcTools.Retired', 'ProtocolProof.Retired', 'Tests.Retired'])
def test_partial_or_retired_module_prefix_is_unowned(module):
    from support.packages import is_owned_module, module_owner
    assert not is_owned_module(module)
    with pytest.raises(ValueError): module_owner(module)


def test_selection_retires_old_keys_and_resolves_diamond_once():
    from support.packages import selected
    assert selected(['verification']) == ['program', 'ir', 'protocol', 'verification']
    assert selected(['applications']) == selected()
    for old in ('main', 'proof', 'security'):
        with pytest.raises(ValueError, match='unknown Lean packages'): selected([old])


@pytest.mark.parametrize('module', ['Zkc.Applications.Clean.NativeClients',
                                    'Zkc.Applications.ArkLib.Subjects.Sumcheck.Evidence',
                                    'Zkc.Applications.Security.Subjects.Schnorr.Evidence'])
def test_concrete_clients_are_owned_downstream_of_adapters(module):
    from support.packages import module_owner, DEPENDENCIES
    assert module_owner(module) == 'applications'
    for adapter in ('arklib', 'clean'):
        assert 'applications' not in DEPENDENCIES[adapter]


@pytest.mark.parametrize('prefix', ['Zkc', 'Zkc.Tools', 'Zkc.Adapters', 'Zkc.Tools.Program'])
def test_library_globs_refuse_broad_or_foreign_prefixes(prefix):
    from support.packages import library_globs
    config = {'lean_lib': [{'roots': ['Zkc.IR'], 'globs': [prefix + '.+']}]}
    with pytest.raises(ValueError): library_globs('ir', config)


def test_package_cli_selection_is_repeatable_and_exclusive():
    import argparse
    from support.packages import add_selection, selection, selected
    parser = argparse.ArgumentParser()
    add_selection(parser)
    args = parser.parse_args(['--package', 'ir', '--package', 'protocol'])
    assert selection(args) == ['program', 'ir', 'protocol']
    assert selection(parser.parse_args([])) == selected()
    assert selection(parser.parse_args(['--core-only'])) == ['program', 'ir', 'protocol', 'verification']
    for arguments in (['--package', 'main'], ['--core-only', '--package', 'ir'], ['--main-only']):
        with pytest.raises(SystemExit): parser.parse_args(arguments)


def test_actual_sources_are_partitioned_into_library_and_isolated_command_audits():
    import tomllib
    from checks import audit_imports
    from support.packages import PACKAGES, package_modules

    for name, (directory, _) in PACKAGES.items():
        modules = set(package_modules(name))
        config = tomllib.loads((directory / 'lakefile.toml').read_text())
        commands = {entry['root'] for entry in config.get('lean_exe', [])}
        assert commands <= modules
        outputs = audit_imports.expected(name)
        library = next(text for path, text in outputs.items() if path.name == 'LibraryImports.lean')
        imported = {line.removeprefix('import ') for line in library.splitlines() if line.startswith('import ')}
        generated = {module for module in modules if module.startswith('Zkc.Tests.') and (
            module.rsplit('.', 1)[-1] in {'Audit', 'LibraryImports', 'ProgramAudit'} or
            '.CommandAudits.' in module)}
        assert not imported & commands
        assert imported | commands == modules - generated, name
        isolated = [text for path, text in outputs.items() if 'CommandAudits' in path.parts]
        assert len(isolated) == len(commands)
        for command in commands:
            matching = [text for text in isolated if f'import {command}\n' in text]
            assert len(matching) == 1, command
            assert f'let families : List Lean.Name := [`{command}]' in matching[0]
            assert '"COMMAND-AUDIT-PASS"' in matching[0]
            assert '!imported.importAll' in matching[0]
            assert all(f'import {other}\n' not in matching[0] for other in commands - {command})


def test_registry_module_owners_and_declaration_names_survive_relocation():
    from checks import audit_imports
    from support.packages import module_owner, module_path

    for module, owner, namespace in (
        ('Zkc.Verification.Claims.Registry', 'verification', 'ZkcSecurity.Registry'),
        ('Zkc.Applications.ArkLib.Registry', 'applications', 'ZkcArkLib.Registry'),
    ):
        assert module_owner(module) == owner
        source = module_path(module).read_text()
        assert f'namespace {namespace}\n' in source
        assert 'def audited : List (String × Option Name × Bool) :=' in source
        assert 'entries.map fun entry => (entry.identifier, entry.schema, entry.category.proposition)' in source
        library = next(text for path, text in audit_imports.expected(owner).items() if path.name == 'LibraryImports.lean')
        assert f'import {module}\n' in library


@pytest.mark.parametrize('package,registry', [
    ('protocol', None), ('verification', 'ZkcSecurity.Registry.table'),
    ('arklib', None), ('applications', 'ZkcArkLib.Registry.reportTable'),
])
def test_record_emitter_requests_only_registries_available_in_selected_package(monkeypatch, tmp_path, package, registry):
    from types import SimpleNamespace
    from records import declarations

    calls = []
    def run(command, **kwargs):
        calls.append(command)
        if command[1] == 'env':
            index = next(i for i, arg in enumerate(command) if str(arg).endswith('.jsonl'))
            families = ['.'.join(Path(arg).with_suffix('').parts) for arg in command[index + 1:]]
            header = dict(format=declarations.FORMAT, families=families, modules=len(families), declarations=0,
                          axiom_provenance='resolved-constant-info/0', reference_provenance='checked-stored-module/0')
            Path(command[index]).write_text(json.dumps(header) + '\n')
        return SimpleNamespace(returncode=0)
    # This control checks CLI registry selection, independently of Lean parsing.
    headers = SimpleNamespace(imports=lambda *_: [])
    monkeypatch.setattr(declarations, 'HeaderParser', lambda **_: nullcontext(headers))
    monkeypatch.setattr(declarations.subprocess, 'run', run)
    assert declarations.emit(package, tmp_path / 'records.jsonl').returncode == 0
    command = calls[-1]
    if registry is None:
        assert '--registry' not in command
        assert '--endpoints' not in command
    else:
        assert command[command.index('--registry') + 1] == registry
        namespace = registry.rsplit('.', 1)[0]
        endpoint = 'reportEndpoints' if package == 'applications' else 'endpoints'
        assert command[command.index('--endpoints') + 1] == namespace + '.' + endpoint


def declaration_shard(path, families, rows):
    from records.declarations import FORMAT
    header = dict(format=FORMAT, families=families, modules=len(families), declarations=len(rows),
                  axiom_provenance='resolved-constant-info/0', reference_provenance='checked-stored-module/0')
    path.write_text(''.join(json.dumps(row) + '\n' for row in [header, *rows]))
    return path


@pytest.mark.parametrize('code', [-15, 1])
@pytest.mark.parametrize('stage', range(4))
def test_record_emitter_propagates_failed_builds_and_captures_without_publishing(monkeypatch, tmp_path, code, stage):
    import subprocess
    from types import SimpleNamespace
    from records import declarations

    commands = []
    failed = subprocess.CompletedProcess(['failed-stage'], code)
    def run(command, **kwargs):
        commands.append(command)
        return failed if len(commands) == stage + 1 else subprocess.CompletedProcess(command, 0)
    headers = SimpleNamespace(imports=lambda *_: [])
    monkeypatch.setattr(declarations, 'HeaderParser', lambda **_: nullcontext(headers))
    monkeypatch.setattr(declarations.subprocess, 'run', run)
    output = tmp_path / 'records.jsonl'
    output.write_text('previous complete records\n')
    assert declarations.emit('applications', output) is failed
    assert len(commands) == stage + 1
    assert output.read_text() == 'previous complete records\n'


def test_isolated_records_preserve_private_rows_and_each_commands_main(tmp_path):
    from records.declarations import merge_emissions
    common = [{'module': 'Common', 'name': 'privateHelper', 'tags': ['private'], 'body': body}
              for body in ('first', 'second')]
    parts = [(declaration_shard(tmp_path / 'common.jsonl', ['Common'], common), ['Common'], ['Common'])]
    for module in ('FirstCommand', 'SecondCommand'):
        context = ['Common', module]
        rows = [*common, {'module': module, 'name': 'main'}]
        parts.append((declaration_shard(tmp_path / f'{module}.jsonl', context, rows), context, [module]))
    output = tmp_path / 'merged.jsonl'
    merge_emissions(parts, output)
    header, *rows = [json.loads(line) for line in output.read_text().splitlines()]
    assert header['families'] == ['Common', 'FirstCommand', 'SecondCommand']
    assert header['modules'] == 3 and header['declarations'] == 4
    assert [row for row in rows if row['name'] == 'privateHelper'] == common
    assert {row['module'] for row in rows if row['name'] == 'main'} == {'FirstCommand', 'SecondCommand'}


@pytest.mark.parametrize('defect', ['missing-source', 'unselected-record', 'duplicate-source',
                                  'wrong-count', 'different-registry'])
def test_isolated_records_refuse_incomplete_or_inconsistent_shards(tmp_path, defect):
    from records.declarations import merge_emissions
    path = declaration_shard(tmp_path / 'first.jsonl', ['First'], [{'module': 'First', 'name': 'main'}])
    second = declaration_shard(tmp_path / 'second.jsonl', ['Second'], [{'module': 'Second', 'name': 'main'}])
    parts = [(path, ['First'], ['First']), (second, ['Second'], ['Second'])]
    header, row = [json.loads(line) for line in second.read_text().splitlines()]
    if defect == 'missing-source':
        header['families'] = []
    elif defect == 'unselected-record':
        row['module'] = 'Other'
    elif defect == 'duplicate-source':
        parts.append(parts[0])
    elif defect == 'wrong-count':
        header['declarations'] = 0
    else:
        header['registry'] = [{'identifier': 'changed-schema', 'schema': 'Wrong.predicate'}]
    second.write_text(json.dumps(header) + '\n' + json.dumps(row) + '\n')
    with pytest.raises(ValueError):
        merge_emissions(parts, tmp_path / 'merged.jsonl')
