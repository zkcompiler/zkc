"""Reverse consumer selection uses manifests and fails conservatively."""

import pytest

import smoke


@pytest.fixture
def repository(tmp_path, monkeypatch):
    matrix = {name: {'projects': [name], 'cases': [f'test_{name}.py']} for name in ('one', 'two', 'three')}
    monkeypatch.setattr(smoke, 'MATRIX', matrix)
    for name in matrix:
        project = tmp_path / 'examples/projects' / name
        project.mkdir(parents=True)
        dependency = 'shared' if name != 'three' else 'separate'
        (project / 'zkc.toml').write_text(f'''format="zkc.project/0"
[modules]
"{name}"="main.zkc"
[dependencies]
base="../../../libraries/{dependency}"
''')
    for name in ('shared', 'separate'):
        package = tmp_path / 'libraries' / name
        package.mkdir(parents=True)
        (package / 'zkc.toml').write_text(f'format="zkc.project/0"\n[modules]\n"{name}"="lib.zkc"\n')
    return tmp_path


@pytest.mark.parametrize('path,expected', [
    ('libraries/shared/lib.zkc', {'one', 'two'}),
    ('libraries/shared/zkc.toml', {'one', 'two'}),
    ('libraries/separate/lib.zkc', {'three'}),
    ('examples/projects/one/inputs/P.json', {'one'}),
    ('examples/projects/one/README.md', {'one'}),
    ('common/tests/protocol/test_two.py', {'two'}),
    ('compiler/lib/Language/Check.cpp', {'one', 'two', 'three'}),
    ('common/tests/support/input_files.py', {'one', 'two', 'three'}),
    ('libraries/unclassified/lib.zkc', {'one', 'two', 'three'}),
    ('docs/architecture.md', set()),
])
def test_manifest_consumers(repository, path, expected):
    assert smoke.select_families([path], repository) == expected


def test_deleted_manifest_and_unknown_base_select_all(repository):
    (repository / 'libraries/shared/zkc.toml').unlink()
    assert smoke.select_families(['libraries/shared/zkc.toml'], repository) == {'one', 'two', 'three'}
    assert smoke.select_families(None, repository) == {'one', 'two', 'three'}


def test_selected_and_unclassified_changes_select_all(repository):
    assert smoke.select_families(['libraries/separate/lib.zkc', 'unknown.source'], repository) == {'one', 'two', 'three'}


def test_catalog_changes_select_users_and_missing_keys_select_all(repository):
    project = repository / 'examples/projects/one/zkc.toml'
    project.write_text('''format="zkc.project/0"
[workspace]
path="../../../zkc.workspace.toml"
[dependencies]
base={workspace="shared"}
''')
    catalog = repository / 'zkc.workspace.toml'
    catalog.write_text('format="zkc.workspace/0"\n[packages]\nshared="libraries/shared"\nunused="absent"\n')
    assert smoke.select_families(['zkc.workspace.toml'], repository) == {'one'}
    assert smoke.select_families(['libraries/shared/lib.zkc'], repository) == {'one', 'two'}
    catalog.write_text('format="zkc.workspace/0"\n[packages]\nother="absent"\n')
    assert smoke.select_families(['zkc.workspace.toml'], repository) == {'one', 'two', 'three'}
