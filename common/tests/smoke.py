"""Compact native coverage and conservative selection from manifest consumers."""

import json
from pathlib import Path

from project import project_inputs

ROOT = Path(__file__).resolve().parents[2]
MATRIX = json.loads((Path(__file__).with_suffix('.json')).read_text())


def cases(families):
    selected = {f'common/tests/protocol/{case}' for family in sorted(families)
                for case in MATRIX[family]['cases']}
    if selected:
        selected.add('common/tests/protocol/test_library_packages.py')
    for family in families:
        for project in MATRIX[family]['projects']:
            selected.add('common/tests/protocol/test_example_recipes.py::'
                         'test_readme_recipe_runs_in_a_clean_consumer'
                         f'[examples/projects/{project}]')
    return sorted(selected)


def select_families(paths, root=ROOT):
    """Select reverse manifest consumers; uncertainty always selects all cases.

    The matrix owns test selection only. Module ownership and dependency edges
    come from the projects' manifests, including their transitive dependencies.
    Deleted or unreadable manifests and unclassified source changes select all.
    """
    all_families = set(MATRIX)
    if paths is None:
        return all_families
    relevant = [path for path in paths if not path.endswith('.md') or
                path.startswith(('examples/', 'libraries/'))]
    if not relevant:
        return set()
    consumers = {}
    try:
        for family, spec in MATRIX.items():
            owned = set()
            for project in spec['projects']:
                manifest = root / 'examples/projects' / project / 'zkc.toml'
                manifests = []
                modules, assets = project_inputs(manifest, manifests=manifests)
                owned.update(path.resolve() for path in modules.values())
                owned.update(path.resolve() for _, path in assets.values())
                owned.update(manifests)
            consumers[family] = owned
    except (OSError, ValueError, AssertionError):
        return all_families
    selected = set()
    for path in relevant:
        absolute = (root / path).resolve()
        matching = {family for family, owned in consumers.items() if absolute in owned}
        for family, spec in MATRIX.items():
            if any(path.startswith(f'examples/projects/{project}/') for project in spec['projects']):
                matching.add(family)
            if any(path == f'common/tests/protocol/{case.split("::")[0]}' for case in spec['cases']):
                matching.add(family)
        if not matching:
            return all_families
        selected.update(matching)
    return selected
