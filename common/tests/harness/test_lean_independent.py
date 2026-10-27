"""Independent export policy, artifact identity, and bounded process controls."""

import json
from pathlib import Path
import sys

import pytest

from harness import ROOT, load


def checker():
    return load('lean_independent', 'lean/checks/check_independent.py')


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data))


@pytest.fixture
def configured(tmp_path):
    audit = checker()
    root = tmp_path / 'lean'
    lock = {'format': 'zkc.claims-lock/0', 'theorems': {}}
    for package, subdir in audit.PACKAGES.items():
        name = f'{package}.locked'
        lock['theorems'][name] = {'package': package, 'module': f'{package}.Module'}
        write(root / subdir / 'comparator.json', {
            'challenge_module': 'LockedStatements', 'solution_module': 'LockedStatements',
            'theorem_names': [name], 'definition_names': [], 'permitted_axioms': audit.AXIOMS})
    write(root / 'checks/claims.lock.json', lock)
    return audit, root


def artifacts(audit, root, directory, legacy=False):
    directory.mkdir()
    groups = audit.configuration(root)
    rows = {}
    for package, group in groups.items():
        target = directory / f'{package}.ndjson'
        target.write_text(json.dumps({'in': 1, 'str': {'pre': 0, 'str': package}}) + '\n' +
                          json.dumps({'in': 2, 'str': {'pre': 1, 'str': 'locked'}}) + '\n' +
                          json.dumps({'thm': {'name': 2}}) + '\n')
        rows[package] = {'file': target.name, 'theorems': group['theorems'],
                         'sha256': audit.digest(target), 'bytes': target.stat().st_size,
                         'modules': group['modules'], 'inputs': {}, 'comparator_sha256': audit.digest(group['config']),
                         'command': ['lake', 'env', 'leanexport']}
        if legacy:
            rows[package].update(source='a' * 40, seconds=0)
            for field in ['file', 'modules', 'inputs', 'comparator_sha256']:
                del rows[package][field]
    manifest = rows if legacy else {
        'format': audit.CAPTURE_FORMAT, 'created_utc': '2026-10-26T00:00:00Z',
        'source': {'revision': 'b' * 40, 'status': '', 'diff_sha256': 'a' * 64},
        'toolchain': {'version': 'test', 'binaries': {}}, 'lock_sha256': audit.digest(root / 'checks/claims.lock.json'),
        'packages': rows, 'commands': []}
    write(directory / 'manifest.json', manifest)
    return directory / 'manifest.json'


def test_repository_covers_all_116_locked_declarations():
    groups = checker().configuration(ROOT / 'lean')
    assert {p: len(g['theorems']) for p, g in groups.items()} == {
        'main': 49, 'security': 40, 'arklib': 24, 'clean': 3}


@pytest.mark.parametrize('defect', ['missing', 'extra', 'duplicate', 'hole', 'axiom', 'unknown-field', 'module'])
def test_comparator_cannot_reduce_or_expand_policy(configured, defect):
    audit, root = configured
    path = root / 'security/comparator.json'
    config = audit.read_json(path)
    if defect == 'missing': config['theorem_names'] = []
    if defect == 'extra': config['theorem_names'].append('unlocked')
    if defect == 'duplicate': config['theorem_names'] *= 2
    if defect == 'hole': config['definition_names'] = ['allowedHole']
    if defect == 'axiom': config['permitted_axioms'] = [*audit.AXIOMS, 'sorryAx']
    if defect == 'unknown-field': config['enable_nanoda'] = False
    if defect == 'module': config['challenge_module'] = '--ignore-missing'
    write(path, config)
    with pytest.raises(audit.CheckError):
        audit.configuration(root)


@pytest.mark.parametrize('defect', ['unknown-package', 'missing-module', 'empty', 'wrong-type'])
def test_lock_validation(configured, defect):
    audit, root = configured
    path = root / 'checks/claims.lock.json'
    lock = audit.read_json(path)
    if defect == 'unknown-package': lock['theorems']['main.locked']['package'] = 'other'
    if defect == 'missing-module': del lock['theorems']['main.locked']['module']
    if defect == 'empty': lock['theorems'] = {}
    if defect == 'wrong-type': lock['theorems'] = ['main.locked']
    write(path, lock)
    with pytest.raises(audit.CheckError):
        audit.configuration(root)


def test_duplicate_json_keys_are_rejected(tmp_path):
    audit = checker()
    path = tmp_path / 'policy.json'
    path.write_text('{"permitted_axioms": [], "permitted_axioms": ["sorryAx"]}')
    with pytest.raises(audit.CheckError, match='duplicate JSON key'):
        audit.read_json(path)


@pytest.mark.parametrize('defect', ['missing-package', 'coverage', 'digest', 'size', 'missing-file', 'traversal',
                                  'provenance', 'format', 'unknown-field', 'toolchain-version'])
def test_artifact_validation(configured, tmp_path, defect):
    audit, root = configured
    path = artifacts(audit, root, tmp_path / 'capture')
    manifest = audit.read_json(path)
    row = manifest['packages']['clean']
    if defect == 'missing-package': del manifest['packages']['clean']
    if defect == 'coverage': row['theorems'] = []
    if defect == 'digest': row['sha256'] = '0' * 64
    if defect == 'size': row['bytes'] += 1
    if defect == 'missing-file': (path.parent / 'clean.ndjson').unlink()
    if defect == 'traversal': row['file'] = '../clean.ndjson'
    if defect == 'provenance': del manifest['source']
    if defect == 'format': manifest['format'] = 'unsupported'
    if defect == 'unknown-field': manifest['unchecked'] = True
    if defect == 'toolchain-version': del manifest['toolchain']['version']
    write(path, manifest)
    with pytest.raises(audit.CheckError):
        audit.load_artifacts(path, audit.configuration(root), list(audit.PACKAGES))


def test_unversioned_manifest_is_rejected(configured, tmp_path):
    audit, root = configured
    path = artifacts(audit, root, tmp_path / 'baseline', legacy=True)
    with pytest.raises(audit.CheckError, match='unsupported'):
        audit.load_artifacts(path, audit.configuration(root), list(audit.PACKAGES))


def test_loaded_exports_are_bounded_before_checking(configured, tmp_path):
    audit, root = configured
    path = artifacts(audit, root, tmp_path / 'capture')
    with pytest.raises(audit.CheckError, match='export output limit'):
        audit.load_artifacts(path, audit.configuration(root), ['main'], export_limit=1)


@pytest.mark.parametrize('alias', ['manifest', 'symlink', 'hardlink'])
def test_self_comparisons_are_rejected_before_tools(configured, tmp_path, alias):
    audit, root = configured
    base = artifacts(audit, root, tmp_path / 'base')
    candidate = artifacts(audit, root, tmp_path / 'candidate')
    if alias == 'manifest': candidate = base
    else:
        target = candidate.parent / 'main.ndjson'
        target.unlink()
        if alias == 'symlink': target.symlink_to(base.parent / 'main.ndjson')
        else: target.hardlink_to(base.parent / 'main.ndjson')
    with pytest.raises(audit.CheckError, match='independent artifacts'):
        audit.compare(root, audit.configuration(root), ['main'], tmp_path, 'unavailable', None, base, candidate)


def test_every_export_explicitly_includes_primitives_and_axioms(configured):
    audit, root = configured
    group = audit.configuration(root)['security']
    command = audit.export_command('lake', Path('/toolchain/bin/leanexport'), group)
    assert command[:3] == ['lake', 'env', '/toolchain/bin/leanexport']
    assert command[3:command.index('--')] == ['security.Module']
    assert command[command.index('--') + 1:] == group['theorems'] + audit.AXIOMS + audit.PRIMITIVES
    assert {'Nat.xor', 'semiOutParam', 'Quot.sound'} <= set(command)


@pytest.mark.parametrize('defect', ['missing-kernel', 'wrong-version', 'internal-export', 'empty-internal-export'])
def test_tools_cannot_be_silently_omitted_or_version_mixed(configured, tmp_path, monkeypatch, defect):
    audit, root = configured
    prefix = tmp_path / 'toolchain'
    (prefix / 'bin').mkdir(parents=True)
    for name in ['lake', 'lean', 'leanexport', *audit.CHECKERS]:
        if name == 'con-ron' and defect == 'missing-kernel': continue
        binary = prefix / 'bin' / name
        binary.write_text('test executable')
        binary.chmod(0o755)
    if defect == 'internal-export': monkeypatch.setenv('LAKE_CHECK_EXPORT', '1')
    if defect == 'empty-internal-export': monkeypatch.setenv('LAKE_CHECK_EXPORT', '')

    class Tools:
        def run(self, command, cwd, label):
            if label == 'toolchain-prefix': return str(prefix)
            return 'Lean (version 4.34.1, test)' if defect == 'wrong-version' else 'Lean (version 4.35.0, test)'

    with pytest.raises(audit.CheckError, match={
            'missing-kernel': 'missing bundled tool', 'wrong-version': 'unsupported toolchain',
            'internal-export': 'unset LAKE_CHECK_EXPORT',
            'empty-internal-export': 'unset LAKE_CHECK_EXPORT'}[defect]):
        audit.tools_for(root, 'lake', Tools(), paranoid=True)


@pytest.mark.parametrize('failure', ['comparator', 'paranoid', 'mutation', None])
def test_export_only_wiring_and_failure_receipts(configured, tmp_path, monkeypatch, failure):
    # These are orchestration tests; semantic rejection controls live in lean/checks/tests.
    audit, root = configured
    base = artifacts(audit, root, tmp_path / 'base')
    candidate = artifacts(audit, root, tmp_path / 'candidate')
    monkeypatch.setattr(audit, 'tools_for', lambda *a, **k: (Path('/bundled'), {'version': 'test'}))

    class RecordingRunner:
        commands = []

        def run(self, command, cwd, label):
            self.commands.append(command)
            if label.endswith(f'-{failure}'):
                raise audit.CheckError(f'{failure} rejection')
            if label.endswith('-paranoid') and failure == 'mutation':
                (candidate.parent / 'main.ndjson').write_text('changed')

    runner = RecordingRunner()
    output = tmp_path / 'report'
    output.mkdir()
    if failure:
        with pytest.raises(audit.CheckError):
            audit.compare(root, audit.configuration(root), ['main'], output, 'lake', runner, base, candidate)
    else:
        audit.compare(root, audit.configuration(root), ['main'], output, 'lake', runner, base, candidate)
    report = audit.read_json(output / 'report.json')
    assert report['status'] == ('failed' if failure else 'passed')
    assert runner.commands[0][1:] == ['comparator', '--config', str(output / 'main-comparator.json'),
                                      '--challenge-from-export', str(base.parent / 'main.ndjson'),
                                      '--solution-from-export', str(candidate.parent / 'main.ndjson')]
    if failure != 'comparator':
        assert runner.commands[1][1:] == ['check', '--paranoid', '--from-export', str(candidate.parent / 'main.ndjson')]
    assert not any('build' in command or '--inadvisably-no-sandbox' in command for command in runner.commands)


def test_cli_requires_explicit_base_and_candidate_and_rejects_overwrite(configured, tmp_path):
    audit, root = configured
    output = tmp_path / 'already-there'
    output.mkdir()
    with pytest.raises(SystemExit):
        audit.main(['compare', '--output', str(output)])
    with pytest.raises(SystemExit):
        audit.main(['capture', '--output', str(output), '--replay-toolset', 'tools.json'])
    with pytest.raises(SystemExit):
        audit.main(['replay', '--output', str(output), '--base-manifest', 'base.json'])
    assert audit.main(['capture', '--lean-root', str(root), '--output', str(output)]) == 1
    assert list(output.iterdir()) == []


@pytest.mark.parametrize('failure', ['exit', 'log', 'combined', 'export', 'timeout', 'memory'])
def test_process_failures_remain_failures_and_outputs_are_bounded(tmp_path, failure):
    audit = checker()
    runner = audit.Runner(tmp_path, memory_mb=256, log_mb=1, export_mb=1, timeout=1)
    code = {'exit': 'import sys; sys.exit(7)',
            'log': 'import os; os.write(2, b"x" * 2000000)',
            'combined': 'import os; os.write(1, b"x" * 600000); os.write(2, b"x" * 600000)',
            'export': 'import os; os.write(1, b"x" * 2000000)',
            'timeout': 'import time; time.sleep(10)',
            'memory': 'bytearray(512 * 1024**2)'}[failure]
    target = tmp_path / 'out.ndjson' if failure == 'export' else None
    with pytest.raises(audit.CheckError, match={'exit': 'exited 7', 'log': 'log output limit',
                                             'combined': 'log output limit',
                                             'export': 'export output limit', 'timeout': 'timeout',
                                             'memory': 'exited 1'}[failure]):
        runner.run([sys.executable, '-c', code], tmp_path, 'child', export=target)
    assert (tmp_path / 'child.log').stat().st_size <= 1024**2
    if target: assert target.stat().st_size <= 1024**2


def test_missing_command_is_not_acceptance(tmp_path):
    with pytest.raises(OSError):
        checker().Runner(tmp_path).run(['/missing/command'], tmp_path, 'missing')


@pytest.fixture
def toolset(tmp_path, monkeypatch):
    audit = checker()
    root = tmp_path / 'tools'
    stock = tmp_path / 'stock'
    pins = {'sources': {'lean/Replay.lean': 'unused'}, 'patches': []}
    recipe = tmp_path / 'recipe.json'
    write(recipe, pins)
    monkeypatch.setattr(audit, 'REPLAY_SOURCES', recipe)
    source = root / 'sources/lean/Replay.lean'
    source.parent.mkdir(parents=True)
    source.write_text('pinned source')
    pins['sources']['lean/Replay.lean'] = audit.digest(source)
    write(recipe, pins)
    runtime, installed = {}, {}
    for name in audit.RUNTIME_FILES:
        for directory in [root / 'sysroot', stock]:
            file = directory / name
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text('stock ' + name)
            file.chmod(0o755)
        installed[name] = audit.identity(stock / name)[0]
        if name in {f'bin/{n}' for n in audit.PATCHED_CHECKERS}:
            (root / 'sysroot' / name).write_text('patched ' + name)
        runtime[name] = audit.identity(root / 'sysroot' / name)[0]
    receipt = {'format': audit.TOOLSET_FORMAT, 'label': 'patched Lean 4.35.0 replay',
               'recipe_sha256': audit.digest(recipe),
               'builder_sha256': audit.digest(ROOT / 'lean/checks/build_replay_tools.py'),
               'inputs': {'toolchain': installed, 'sources': pins['sources'], 'patches': []},
               'commands': [{'command': ['pinned-build'], 'exit_code': 0}], 'runtime': runtime, 'reuse': None}
    write(root / 'manifest.json', receipt)
    return audit, root, stock


@pytest.mark.parametrize('defect', ['recipe', 'source', 'binary', 'library', 'stock', 'missing-checker',
                                  'extra-file', 'symlink-file', 'symlink-directory', 'commands',
                                  'unknown-field', 'path', 'executable'])
def test_replay_toolset_cannot_change_recipe_stock_tools_or_omit_checkers(toolset, defect):
    audit, root, stock = toolset
    path = root / 'manifest.json'
    receipt = audit.read_json(path)
    target = root / 'sysroot/bin/lean4lean'
    if defect == 'recipe': receipt['recipe_sha256'] = '0' * 64
    if defect == 'source': (root / 'sources/lean/Replay.lean').write_text('changed source')
    if defect == 'binary': target.write_text('changed binary')
    if defect == 'library':
        target = root / 'sysroot/lib/lean/libleanshared.so'
        target.write_text('changed library')
        receipt['runtime']['lib/lean/libleanshared.so'] = audit.identity(target)[0]
    if defect == 'stock': (stock / 'bin/lake').write_text('changed stock lake')
    if defect == 'missing-checker': del receipt['runtime']['bin/con-ron']
    if defect == 'extra-file': (root / 'sysroot/bin/unreviewed').write_text('extra')
    if defect == 'symlink-file':
        target.unlink()
        target.symlink_to(stock / 'bin/lean4lean')
    if defect == 'symlink-directory':
        (root / 'sysroot/lib').rename(root / 'libraries')
        (root / 'sysroot/lib').symlink_to(root / 'libraries', target_is_directory=True)
    if defect == 'commands': receipt['commands'] = []
    if defect == 'unknown-field': receipt['unchecked'] = True
    if defect == 'path': receipt['runtime']['../bin/lean4lean'] = receipt['runtime'].pop('bin/lean4lean')
    if defect == 'executable': target.chmod(0o644)
    write(path, receipt)
    with pytest.raises(audit.CheckError):
        audit.replay_toolset(path, stock)


@pytest.mark.parametrize('mutation', ['replace', 'restore-bytes', 'symlink-parent', 'transient-library'])
def test_replay_runtime_snapshot_detects_changes_even_when_bytes_match(toolset, tmp_path, mutation):
    audit, root, stock = toolset
    output = tmp_path / 'report'
    output.mkdir()
    runner = audit.Runner(output)
    prefix, provenance = audit.select_replay_toolset(root / 'manifest.json', stock, {'version': 'test'}, output, runner)
    target = prefix / 'bin/lean4lean'
    original = target.read_bytes()
    assert not target.samefile(root / 'sysroot/bin/lean4lean')
    assert provenance['replay_toolset']['provenance']['label'] == 'patched Lean 4.35.0 replay'
    if mutation == 'replace':
        target.unlink()
        target.write_bytes(original)
    elif mutation == 'restore-bytes':
        target.chmod(0o755)
        target.write_bytes(b'changed')
        target.write_bytes(original)
        target.chmod(0o555)
    elif mutation == 'symlink-parent':
        (prefix / 'bin').rename(prefix / 'renamed')
        (prefix / 'bin').symlink_to(prefix / 'renamed', target_is_directory=True)
    else:
        injected = prefix / 'lib/lean/libc.so.6'
        injected.write_text('extra loader input')
        injected.unlink()
    with pytest.raises(audit.CheckError, match='changed during checking'):
        runner.run([sys.executable, '-c', 'pass'], output, 'must-not-start')
    assert not (output / 'must-not-start.log').exists()


@pytest.mark.parametrize('variable', ['LAKE_CHECK_EXPORT', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN',
                                      'LEAN', 'LAKE_HOME', 'LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'])
def test_inherited_environment_cannot_redirect_checked_toolset(monkeypatch, variable):
    audit = checker()
    monkeypatch.setenv(variable, '')
    with pytest.raises(audit.CheckError, match=f'unset {variable}'):
        audit.checking_environment()


@pytest.mark.parametrize('failure', [True, False])
def test_replay_has_separate_verdict_and_retains_full_lake_check(configured, tmp_path, monkeypatch, failure):
    audit, root = configured
    candidate = artifacts(audit, root, tmp_path / 'candidate')
    monkeypatch.setattr(audit, 'tools_for', lambda *a, **k: (Path('/bundled'), {'version': 'test'}))

    class RecordingRunner:
        commands = []

        def run(self, command, cwd, label):
            self.commands.append(command)
            if failure: raise audit.CheckError('kernel rejection')

    runner = RecordingRunner()
    output = tmp_path / 'report'
    output.mkdir()
    if failure:
        with pytest.raises(audit.CheckError):
            audit.replay(root, audit.configuration(root), ['main'], output, 'lake', runner, candidate)
    else:
        audit.replay(root, audit.configuration(root), ['main'], output, 'lake', runner, candidate)
    report = audit.read_json(output / 'report.json')
    assert report['format'] == audit.REPLAY_FORMAT
    assert report['status'] == ('failed' if failure else 'passed')
    assert 'no model comparison or baseline acceptance' in report['scope']
    assert runner.commands == [['/bundled/bin/lake', 'check', '--paranoid', '--from-export',
                                str(candidate.parent / 'main.ndjson')]]


def test_replay_requires_roots_in_export_not_only_manifest(tmp_path):
    audit = checker()
    path = tmp_path / 'export.ndjson'
    path.write_text('{"in":1,"str":{"pre":0,"str":"Unrelated"}}\n{"thm":{"name":1}}\n')
    audit.require_export_roots(path, ['Unrelated'])
    with pytest.raises(audit.CheckError, match='missing locked export roots'):
        audit.require_export_roots(path, ['Locked.root'])
    path.write_text('not an export')
    with pytest.raises(audit.CheckError, match='malformed export inventory'):
        audit.require_export_roots(path, ['Locked.root'])
    path.write_text('{"in":1,"str":{"pre":0,"str":"Unrelated"}}\n' * 2)
    with pytest.raises(audit.CheckError, match='duplicate root name table entry'):
        audit.require_export_roots(path, ['Unrelated'])
    path.write_text('{"in":1,"str":{"pre":0,"str":"Locked.root"}}\n{"thm":{"name":1}}\n')
    with pytest.raises(audit.CheckError, match='missing locked export roots'):
        audit.require_export_roots(path, ['Locked.root'])
    path.write_text('{"in":1,"in":2,"str":{"pre":0,"str":"Unrelated"}}\n')
    with pytest.raises(audit.CheckError, match='duplicate JSON key'):
        audit.require_export_roots(path, ['Unrelated'])
    path.write_text(' ' * (8 * 1024**2 + 1))
    with pytest.raises(audit.CheckError, match='export record exceeds'):
        audit.require_export_roots(path, ['Locked.root'])
