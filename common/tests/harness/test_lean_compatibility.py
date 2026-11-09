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
    integration = root / 'lean/adapters/arklib'
    result = subprocess.run(['python3', '-c',
        'import json, reproduce; print(json.dumps(reproduce.build_inputs(reproduce.HERE, packages=["arklib"])))'],
        cwd=root / 'lean', capture_output=True, text=True, check=True)
    inputs = json.loads(result.stdout)
    for name in ['compatibility.json', 'compatibility.patch']:
        path = integration / name
        if path.is_file():
            assert inputs['adapters/arklib/' + name] == hashlib.sha256(path.read_bytes()).hexdigest()
        else:
            assert 'adapters/arklib/' + name not in inputs


def test_fresh_reproduction_records_clean_wrapper_and_patch():
    root = Path(__file__).resolve().parents[3]
    result = subprocess.run(['python3', '-c',
        'import json, reproduce; print(json.dumps(reproduce.build_inputs(reproduce.HERE, packages=["applications"])))'],
        cwd=root / 'lean', capture_output=True, text=True, check=True)
    inputs = json.loads(result.stdout)
    for name in ['applications/Zkc/Applications/Clean.lean',
                 'applications/Zkc/Applications/Clean/NativeClients.lean',
                 'adapters/clean/Zkc/Adapters/Clean/NativeExport.lean',
                 'adapters/clean/compatibility.json', 'adapters/clean/compatibility.patch']:
        path = root / 'lean' / name
        assert inputs[name] == hashlib.sha256(path.read_bytes()).hexdigest()


def test_clean_control_runs_with_package_options_before_its_filename(tmp_path, monkeypatch):
    reproduce = load('lean_reproduce', 'lean/reproduce.py')
    directory = tmp_path / 'lean/adapters/clean'
    directory.mkdir(parents=True)
    control = directory / 'Zkc/Tests/Clean/Control.lean'
    control.parent.mkdir(parents=True)
    control.write_text('def main : IO Unit := pure ()\n')
    audit = directory / 'Zkc/Tests/Clean/CommandAudits/Clean/Control.lean'
    audit.parent.mkdir(parents=True)
    audit.write_text('import Zkc.Tests.Clean.Control\n')
    expected = tmp_path / 'expected.mlir'
    expected.write_bytes(b'control\n')
    commands = []

    def run(command, **kwargs):
        from types import SimpleNamespace
        commands.append(command)
        return SimpleNamespace(returncode=0, stdout=expected.read_bytes())

    monkeypatch.setattr(reproduce.subprocess, 'run', run)
    result = reproduce.clean_control('lake', directory, expected, tmp_path / 'control.log', {})
    assert result['status'] == 'pass'
    assert commands == [reproduce.lean_command(directory, '-DautoImplicit=false', '-DwarningAsError=true',
                                                '--run', control, lake='lake')]


def test_koala_bear_generator_keeps_fixture_and_output_owners_separate(tmp_path, monkeypatch):
    generator = load('lean_koala_bear_generator', 'lean/verification/checks/generate_koala_bear_sumcheck.py')
    fixture = generator.package_directory('verification') / 'fixtures/koala-bear-sumcheck-round.zkc'
    assert fixture.is_file()
    assert generator.source_format.of_source(fixture) == 'zkc'
    seen = []

    def formats(paths):
        seen.extend(paths)
        return 'zkc'

    def generate(compiler, source, output, report, *, selection):
        assert source == fixture
        assert output == generator.module_package('Zkc.Applications')
        assert selection == 'zkc'
        raise StopIteration('checked the generation boundary')

    monkeypatch.setattr(generator.source_format, 'of_sources', formats)
    monkeypatch.setattr(generator, 'generate', generate)
    monkeypatch.setattr(generator.sys, 'argv', ['generate', '--compiler', str(tmp_path / 'compiler'),
                                               '--report-dir', str(tmp_path / 'report')])
    with pytest.raises(StopIteration, match='generation boundary'):
        generator.main()
    assert seen[0] == fixture


def test_koala_bear_candidate_uses_artifact_overlays_without_mirroring(tmp_path, monkeypatch):
    from types import SimpleNamespace
    generator = load('lean_koala_bear_overlay', 'lean/verification/checks/generate_koala_bear_sumcheck.py')
    output, cache = tmp_path / 'candidate', tmp_path / 'cache'
    (output / generator.MODULE).mkdir(parents=True)
    commands = []

    def run(command, cwd, report, *, env=None, expected=0):
        commands.append((command, env))
        return SimpleNamespace(stdout='/existing/artifacts', returncode=expected or 0)

    monkeypatch.setattr(generator, 'run', run)
    monkeypatch.setattr(generator, 'PRINTER_CACHE', cache)
    generator.check_candidate(output, tmp_path, 'ordered-operands')
    for command, env in commands[1:]:
        assert env['LEAN_PATH'].split(generator.os.pathsep) == [str(output), str(cache), '/existing/artifacts']
        assert command[:2] == generator.lean_command(generator.APPLICATIONS)[:2]
    assert not any(path.is_symlink() for path in output.rglob('*'))
