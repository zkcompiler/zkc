"""Explicit checked dependencies take precedence over inherited cache links."""
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
