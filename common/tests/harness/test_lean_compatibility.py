"""Dependency preparation preserves the declared patch and refuses source drift."""
import difflib
import hashlib
import json
from pathlib import Path
import subprocess

import pytest

from harness import load


@pytest.fixture
def package(tmp_path):
    source = tmp_path / '.lake/packages/Upstream'
    source.mkdir(parents=True)
    subprocess.run(['git', 'init', '--quiet', str(source)], check=True)
    before, after = 'import Old.Module\n', 'import New.Module\n'
    (source / 'Example.lean').write_text(before)
    (source / 'Other.lean').write_text('def unchanged := true\n')
    subprocess.run(['git', '-C', str(source), 'add', 'Example.lean', 'Other.lean'], check=True)
    subprocess.run(['git', '-C', str(source), '-c', 'user.name=Test', '-c',
                    'user.email=test@example.invalid', 'commit', '--quiet', '-m', 'fixture'], check=True)
    revision = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
    patch = ''.join(difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True),
                                        fromfile='a/Example.lean', tofile='b/Example.lean'))
    (tmp_path / 'compatibility.patch').write_text(patch)
    digest = lambda text: hashlib.sha256(text.encode()).hexdigest()  # noqa: E731
    config = {'package': 'Upstream', 'revision': revision, 'patch': 'compatibility.patch',
              'patch_sha256': digest(patch), 'files': {
                  'Example.lean': {'base_sha256': digest(before), 'patched_sha256': digest(after)}}}
    (tmp_path / 'compatibility.json').write_text(json.dumps(config))
    (tmp_path / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages',
        'packages': [{'name': 'Upstream', 'type': 'git', 'rev': revision}]}))
    return tmp_path, source, config


@pytest.fixture
def addition(package):
    """The same fixture with a patch that also adds a new source file."""
    root, source, config = package
    added = 'def added := true\n'
    patch = (root / 'compatibility.patch').read_text() + ''.join(difflib.unified_diff(
        [], added.splitlines(keepends=True), fromfile='/dev/null', tofile='b/Added.lean'))
    patch = patch.replace('--- /dev/null\n+++ b/Added.lean\n',
                          'diff --git a/Added.lean b/Added.lean\nnew file mode 100644\n'
                          '--- /dev/null\n+++ b/Added.lean\n')
    (root / 'compatibility.patch').write_text(patch)
    config['patch_sha256'] = hashlib.sha256(patch.encode()).hexdigest()
    config['files']['Added.lean'] = {'base_sha256': None,
                                     'patched_sha256': hashlib.sha256(added.encode()).hexdigest()}
    (root / 'compatibility.json').write_text(json.dumps(config))
    return root, source, config


def test_patch_reproduces_and_is_idempotent(package):
    root, source, config = package
    compatibility = load('lean_compatibility', 'lean/support/compatibility.py')
    for _ in range(2):
        assert compatibility.prepare(root) == config
        assert (source / 'Example.lean').read_text() == 'import New.Module\n'


@pytest.mark.parametrize('mutation,diagnostic', [
    ('source', 'unexpected dependency source'), ('patch', 'digest mismatch'),
    ('revision', 'revision differs'), ('empty', 'must declare'),
])
def test_patch_refuses_drift(package, mutation, diagnostic):
    root, source, config = package
    if mutation == 'source':
        (source / 'Example.lean').write_text('import Unexpected.Module\n')
    elif mutation == 'patch':
        (root / 'compatibility.patch').write_text('unexpected patch\n')
    else:
        if mutation == 'revision':
            config['revision'] = '0' * 40
        else:
            config['files'] = {}
        (root / 'compatibility.json').write_text(json.dumps(config))
    before = (source / 'Example.lean').read_bytes()
    compatibility = load('lean_compatibility', 'lean/support/compatibility.py')
    with pytest.raises(ValueError, match=diagnostic):
        compatibility.prepare(root)
    assert (source / 'Example.lean').read_bytes() == before


@pytest.mark.parametrize('already_patched', [False, True])
@pytest.mark.parametrize('name', ['Other.lean', 'Untracked.lean'])
def test_patch_refuses_undeclared_sources(package, already_patched, name):
    root, source, _ = package
    compatibility = load('lean_compatibility', 'lean/support/compatibility.py')
    if already_patched:
        compatibility.prepare(root)
    (source / name).write_text('def unexpected := false\n')
    before = (source / 'Example.lean').read_bytes()
    with pytest.raises(ValueError, match='undeclared dependency source changes'):
        compatibility.prepare(root)
    assert (source / 'Example.lean').read_bytes() == before


def test_patch_adds_declared_files_and_is_idempotent(addition):
    root, source, config = addition
    compatibility = load('lean_compatibility', 'lean/support/compatibility.py')
    for _ in range(2):
        assert compatibility.prepare(root) == config
        assert (source / 'Example.lean').read_text() == 'import New.Module\n'
        assert (source / 'Added.lean').read_text() == 'def added := true\n'


@pytest.mark.parametrize('already_patched', [False, True])
def test_patch_refuses_undeclared_sources_beside_added_files(addition, already_patched):
    root, source, _ = addition
    compatibility = load('lean_compatibility', 'lean/support/compatibility.py')
    if already_patched:
        compatibility.prepare(root)
    (source / 'Untracked.lean').write_text('def unexpected := false\n')
    with pytest.raises(ValueError, match='undeclared dependency source changes'):
        compatibility.prepare(root)


def test_patch_refuses_unexpected_added_file(addition):
    root, source, _ = addition
    (source / 'Added.lean').write_text('def added := false\n')
    before = (source / 'Example.lean').read_bytes()
    compatibility = load('lean_compatibility', 'lean/support/compatibility.py')
    with pytest.raises(ValueError, match='unexpected dependency source'):
        compatibility.prepare(root)
    assert (source / 'Example.lean').read_bytes() == before


def test_fresh_reproduction_records_arklib_patch():
    root = Path(__file__).resolve().parents[3]
    integration = root / 'lean/integrations/arklib'
    result = subprocess.run(['python3', '-c',
        'import json, reproduce; print(json.dumps(reproduce.build_inputs(reproduce.HERE, with_arklib=True)))'],
        cwd=root / 'lean', capture_output=True, text=True, check=True)
    inputs = json.loads(result.stdout)
    for name in ['compatibility.json', 'compatibility.patch']:
        path = integration / name
        if path.is_file():
            assert inputs['integrations/arklib/' + name] == hashlib.sha256(path.read_bytes()).hexdigest()
        else:
            assert 'integrations/arklib/' + name not in inputs


def test_fresh_reproduction_records_clean_wrapper_and_patch():
    root = Path(__file__).resolve().parents[3]
    result = subprocess.run(['python3', '-c',
        'import json, reproduce; print(json.dumps(reproduce.build_inputs(reproduce.HERE, with_clean=True)))'],
        cwd=root / 'lean', capture_output=True, text=True, check=True)
    inputs = json.loads(result.stdout)
    for name in ['CleanExamples.lean', 'compatibility.json', 'compatibility.patch',
                 'CleanExamples/NativeClients.lean', 'ZkcClean/NativeExport.lean']:
        path = root / 'lean/integrations/clean' / name
        assert inputs['integrations/clean/' + name] == hashlib.sha256(path.read_bytes()).hexdigest()


def test_clean_control_runs_with_package_options_before_its_filename(tmp_path, monkeypatch):
    reproduce = load('lean_reproduce', 'lean/reproduce.py')
    expected = tmp_path / 'expected.mlir'
    expected.write_bytes(b'control\n')
    commands = []

    def run(command, **kwargs):
        from types import SimpleNamespace
        commands.append(command)
        return SimpleNamespace(returncode=0, stdout=expected.read_bytes())

    monkeypatch.setattr(reproduce.subprocess, 'run', run)
    result = reproduce.clean_control('lake', tmp_path, expected, tmp_path / 'control.log', {})
    assert result['status'] == 'pass'
    assert commands == [['lake', 'env', 'lean', '-DautoImplicit=false', '-DwarningAsError=true',
                         '--run', 'TestsClean/Control.lean']]
