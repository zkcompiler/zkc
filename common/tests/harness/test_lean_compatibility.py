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
    subprocess.run(['git', '-C', str(source), 'add', 'Example.lean'], check=True)
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


def test_fresh_reproduction_records_clean_wrapper_and_patch():
    root = Path(__file__).resolve().parents[3]
    result = subprocess.run(['python3', '-c',
        'import json, reproduce; print(json.dumps(reproduce.build_inputs(reproduce.HERE, with_clean=True)))'],
        cwd=root / 'lean', capture_output=True, text=True, check=True)
    inputs = json.loads(result.stdout)
    for name in ['CleanExamples.lean', 'compatibility.json', 'compatibility.patch',
                 'TestsClean/NativeClients.lean', 'ZkcClean/NativeExport.lean']:
        path = root / 'lean/integrations/clean' / name
        assert inputs['integrations/clean/' + name] == hashlib.sha256(path.read_bytes()).hexdigest()
