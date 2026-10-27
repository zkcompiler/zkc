"""Explicit checked dependencies take precedence over inherited cache links."""
import json
from types import SimpleNamespace

import pytest

from harness import load


def test_explicit_objects_precede_inherited_cache(tmp_path):
    module = load('component_generation_dependencies', 'lean/bridges/structured/generate_component_roots.py')
    first, second, output = (tmp_path / name for name in ('first', 'second', 'output'))
    for directory in (first, second, output):
        (directory / 'Example').mkdir(parents=True)
    stale = tmp_path / 'old.olean'
    stale.write_text('old')
    (first / 'Example/Updated.olean').symlink_to(stale)
    (first / 'Example/First.olean').write_text('first')
    (second / 'Example/Updated.olean').write_text('new')
    (second / 'Example/First.olean').symlink_to(stale)
    (output / 'Example/Updated.olean').symlink_to(stale)
    (output / 'Example/Local.olean').write_text('local')
    (second / 'Example/Local.olean').write_text('dependency')
    generation = module.Generation.__new__(module.Generation)
    generation.dependency_links = set()
    for directory in (first, second):
        generation.overlay(directory, output, owned_only=True)
    for directory in (first, second):
        generation.overlay(directory, output)
    assert (output / 'Example/Updated.olean').read_text() == 'new'
    assert (output / 'Example/First.olean').read_text() == 'first'
    assert (output / 'Example/Local.olean').read_text() == 'local'


def test_failure_summary_keeps_first_error_and_full_log(tmp_path, monkeypatch):
    module = load('component_generation_failure', 'lean/bridges/structured/generate_component_roots.py')
    output = ('Checking a generated proof\n'
              'Example.lean:11:31: error(lean.unknownIdentifier): Unknown identifier `Missing.signature`\n'
              + ('Cascading diagnostic with details\n' * 300)
              + 'Example.lean:90:1: error: last secondary failure\n')
    monkeypatch.setattr(module.subprocess, 'run', lambda *args, **kwargs:
                        SimpleNamespace(returncode=1, stdout=output, stderr=''))
    generation = module.Generation.__new__(module.Generation)
    generation.directory, generation.run_id = tmp_path, 'failure-control'
    generation.environment, generation.commands = {}, []
    with pytest.raises(RuntimeError, match='Missing.signature') as failure:
        generation.execute(['lean', 'Example.lean'])
    assert 'last secondary failure' not in str(failure.value)
    command = json.loads((tmp_path / 'commands.json').read_text())[0]
    assert command['returncode'] == 1
    assert module.Path(command['log']).read_text() == output
