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
        target.write_text(f'{package} test artifact\n')
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


def test_repository_covers_all_88_locked_declarations():
    groups = checker().configuration(ROOT / 'lean')
    assert {p: len(g['theorems']) for p, g in groups.items()} == {
        'main': 41, 'security': 24, 'arklib': 20, 'clean': 3}


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
    assert audit.main(['capture', '--lean-root', str(root), '--output', str(output)]) == 1
    assert list(output.iterdir()) == []


@pytest.mark.parametrize('failure', ['exit', 'log', 'export', 'timeout', 'memory'])
def test_process_failures_remain_failures_and_outputs_are_bounded(tmp_path, failure):
    audit = checker()
    runner = audit.Runner(tmp_path, memory_mb=256, log_mb=1, export_mb=1, timeout=1)
    code = {'exit': 'import sys; sys.exit(7)',
            'log': 'import os; os.write(2, b"x" * 2000000)',
            'export': 'import os; os.write(1, b"x" * 2000000)',
            'timeout': 'import time; time.sleep(10)',
            'memory': 'bytearray(512 * 1024**2)'}[failure]
    target = tmp_path / 'out.ndjson' if failure == 'export' else None
    with pytest.raises(audit.CheckError, match={'exit': 'exited 7', 'log': 'log output limit',
                                             'export': 'export output limit', 'timeout': 'timeout',
                                             'memory': 'exited 1'}[failure]):
        runner.run([sys.executable, '-c', code], tmp_path, 'child', export=target)
    assert (tmp_path / 'child.log').stat().st_size <= 1024**2
    if target: assert target.stat().st_size <= 1024**2


def test_missing_command_is_not_acceptance(tmp_path):
    with pytest.raises(OSError):
        checker().Runner(tmp_path).run(['/missing/command'], tmp_path, 'missing')
