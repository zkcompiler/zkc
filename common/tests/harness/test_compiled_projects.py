"""Preparation sharing must not cross input identities or publish partial builds."""

from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

import pytest

from compiled_projects import CompiledProjects
from journal import Journal, Refused


@pytest.fixture
def project(tmp_path):
    manifest = tmp_path / 'zkc.toml'
    manifest.write_text('format="zkc.project/0"\n[modules]\nmain="main.zkc"\n'
                        '[assets.data]\nformat="relation-bundle-json"\npath="bundle.json"\n')
    (tmp_path / 'main.zkc').write_text('source')
    (tmp_path / 'bundle.json').write_text('asset')
    runtime = tmp_path / 'runtime'
    runtime.write_text(f'#!{sys.executable}\n' + '''import hashlib, json, pathlib, sys, time
args = sys.argv[1:]
project = pathlib.Path(next(x.split('=', 1)[1] for x in args if x.startswith('--project=')))
with project.with_name('compiles').open('a') as stream:
    stream.write('compile\\n')
output = pathlib.Path(next(x.split('=', 1)[1] for x in args if x.startswith('--output=')))
output.write_text('partial')
time.sleep(0.05)
if project.with_name('fail').exists():
    sys.exit(1)
data = json.dumps(args[:args.index(next(x for x in args if x.startswith('--output=')))]).encode()
output.write_bytes(data)
print(json.dumps({'package_sha256': hashlib.sha256(data).hexdigest()}))
''')
    runtime.chmod(0o755)
    compiler = tmp_path / 'compiler'
    compiler.write_text('compiler identity')
    return manifest, SimpleNamespace(runtime=runtime, compiler=compiler)


def consume(root, tools, project, name, *, entry='main::Proof', flags=()):
    journal = Journal(root / 'consumers' / name)
    return CompiledProjects(root / 'shared', tools).compile(project, entry, flags, journal)


def test_workers_publish_one_complete_package_and_retain_provenance(project, tmp_path):
    manifest, tools = project
    script = '''from pathlib import Path
from types import SimpleNamespace
import sys
from compiled_projects import CompiledProjects
from journal import Journal
root, project, compiler, runtime, name = map(Path, sys.argv[1:])
CompiledProjects(root / 'shared', SimpleNamespace(compiler=compiler, runtime=runtime)).compile(
    project, 'main::Proof', (), Journal(root / 'consumers' / name))
'''
    env = dict(os.environ, PYTHONPATH=str(Path(__file__).resolve().parents[1] / 'support'))
    def worker(i):
        return subprocess.run([sys.executable, '-c', script, str(tmp_path), str(manifest),
                               str(tools.compiler), str(tools.runtime), str(i)],
                              env=env, capture_output=True, text=True, timeout=20)
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(worker, range(4)))
    assert all(r.returncode == 0 for r in results), results
    assert (tmp_path / 'compiles').read_text().splitlines() == ['compile']
    references = [json.loads(p.read_text()) for p in (tmp_path / 'consumers').glob('*/preparations/*.json')]
    assert len(references) == 4 and all(r == references[0] for r in references)
    saved = references[0]
    package = Path(saved['package'])
    assert sha256(package.read_bytes()).hexdigest() == saved['sha256']
    assert package.stat().st_mode & 0o222 == 0
    assert json.loads(Path(saved['journal']).read_text())['returncode'] == 0


@pytest.mark.parametrize('change', ['source', 'asset', 'project', 'compiler', 'runtime', 'entry', 'flags', 'run'])
def test_changed_inputs_never_reuse_another_preparation(project, tmp_path, change):
    manifest, tools = project
    first = consume(tmp_path, tools, manifest, 'first')
    args = {}
    second_root = tmp_path
    paths = {'source': manifest.with_name('main.zkc'), 'asset': manifest.with_name('bundle.json'),
             'project': manifest, 'compiler': tools.compiler, 'runtime': tools.runtime}
    if change in paths:
        with paths[change].open('a') as stream:
            stream.write('\n# changed\n')
    elif change == 'entry':
        args['entry'] = 'main::Other'
    elif change == 'flags':
        args['flags'] = ('--no-simplify',)
    else:
        second_root = tmp_path / 'next-run'
    second = consume(second_root, tools, manifest, 'second', **args)
    assert first[0] != second[0]
    assert (tmp_path / 'compiles').read_text().splitlines() == ['compile', 'compile']


def test_failed_compilation_is_kept_but_never_reused(project, tmp_path):
    manifest, tools = project
    failure = tmp_path / 'fail'
    failure.touch()
    with pytest.raises(Refused):
        consume(tmp_path, tools, manifest, 'failed')
    assert not list((tmp_path / 'shared').glob('*/package.json'))
    (record,) = (tmp_path / 'shared').glob('*/compile-*/commands.jsonl')
    assert json.loads(record.read_text())['returncode'] == 1
    failure.unlink()
    package, _ = consume(tmp_path, tools, manifest, 'retry')
    assert package.read_bytes() != b'partial'
    assert (tmp_path / 'compiles').read_text().splitlines() == ['compile', 'compile']


def test_modified_shared_package_fails_instead_of_hiding_interference(project, tmp_path):
    manifest, tools = project
    package, _ = consume(tmp_path, tools, manifest, 'first')
    package.chmod(0o644)
    package.write_text('modified by another consumer')
    with pytest.raises(AssertionError, match='shared package was modified'):
        consume(tmp_path, tools, manifest, 'second')
